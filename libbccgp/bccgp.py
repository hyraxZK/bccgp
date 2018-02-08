#!/usr/bin/python
#
# (C) 2018 Riad S. Wahby <rsw@cs.stanford.edu>
#
# BCCGP implementation

from itertools import chain, izip
import math

from libbccgp.solve import ACSolver

from libfennel.defs import Defs
import libfennel.util as util
from libfennel.fiatshamir import FiatShamir

import pylaurent
from pymiracl import MiraclEC

def _compute_powers(start, inc, n):
    ret = [0] * n
    ret[0] = start
    for i in xrange(1, n):
        ret[i] = (ret[i-1] * inc) % Defs.prime
    return ret

def _generate_powers(start, inc, n):
    val = start
    yield val
    for _ in xrange(1, n):
        val = (val * inc) % Defs.prime
        yield val

# vector x sparse-matrix multiplication (result is a sparse vector)
def _compute_sparse_vec_mat(wq, Yqvec):
    res = {}
    for (qidx, wqi) in enumerate(wq):
        for ridx in wqi:
            res[ridx] = res.get(ridx, 0) + (wqi[ridx] * Yqvec[qidx]) % Defs.prime
    return res

# b is the simplest one: just sum up the generators
def _compute_wib(wq, Yqvec, n, m):
    wvec = _compute_sparse_vec_mat(wq, Yqvec)
    # now sum the values into m lists of length n
    retX = [None] * n
    rets = [None] * m
    for midx in xrange(m):
        rets[midx] = list(retX)
        for nidx in xrange(n):
            rets[midx][nidx] = wvec.get(nidx + n*midx, 0) % Defs.prime
    return rets

# for a, also multiply the ith result vector by y^-i
def _compute_wia(wq, Yqvec, YIvec, n, m):
    wvec = _compute_sparse_vec_mat(wq, Yqvec)
    # now sum values into m lists of length n; for the ith list, multiply by y^-i
    retX = [None] * n
    rets = [None] * m
    for midx in xrange(m):
        rets[midx] = list(retX)
        for nidx in xrange(n):
            rets[midx][nidx] = (wvec.get(nidx + n*midx, 0) * YIvec[midx]) % Defs.prime
    return rets

# for c, subtract y^i * Ypvec from the ith result vector
def _compute_wic(wq, Yqvec, Ypvec, Yvec, n, m):
    wvec = _compute_sparse_vec_mat(wq, Yqvec)
    # now sum values into m lists of length n; for the ith list, subtract y^-i * Ypvec
    retX = [None] * n
    rets = [None] * m
    for midx in xrange(m):
        rets[midx] = list(retX)
        for nidx in xrange(n):
            rets[midx][nidx] = (wvec.get(nidx + n*midx, 0) - Yvec[midx] * Ypvec[nidx]) % Defs.prime
    return rets

class _BCCGPBase(object):
    curve = 'm191'
    K = None
    Kq = None

    def __init__(self, ckt, curve=None):
        self.curve = curve if curve is not None else self.curve
        self.gops = MiraclEC(self.curve)
        util.set_prime(self.gops.q)

        #(waq, wbq, wcq, kq, num_muls) = ckt
        self.ckt = ckt
        self.Q = len(ckt.kq)
        assert len(ckt.waq) == len(ckt.wbq) == len(ckt.wcq) == self.Q

        # dummy values
        self.n = ckt.num_muls
        self.m = 1

    def set_io(self, inputs, outputs):
        self.Kq = [0] * self.Q
        for (idx, kqcoeffs) in enumerate(self.ckt.kq):
            kqval = 0
            for (ionum, coeff) in kqcoeffs.iteritems():
                if ionum < 0:
                    ionum = -1 - ionum
                    # output coeff
                    kqval += coeff * outputs[ionum]
                elif ionum > 0:
                    ionum -= 1
                    kqval += coeff * inputs[ionum]
                else:
                    kqval += coeff
            self.Kq[idx] = kqval % Defs.prime

class _BCCGPSqrt(_BCCGPBase):
    x = None
    Zvec_neg = None
    Zvec_pos = None
    Zvec_last = None
    Xpows_neg = None
    Xpows_pos = None
    y = None
    yInv = None
    Yvec = None
    Ypvec = None
    wai = None
    wbi = None
    wci = None

    def __init__(self, ckt, curve=None):
        super(_BCCGPSqrt, self).__init__(ckt, curve)

        # per BCCGP16 \S5.3, we have
        # m = sqrt(N/3)
        # n = sqrt(3N) = N/m
        # n' = sqrt(7m)
        # m1' = 3 sqrt(m/7) s.t. n' * m1' >= 3m
        # m2' = 4 sqrt(m/7) s.t. n' * m2' >= 4m + 2
        self.m = int(math.ceil(math.sqrt(ckt.num_muls / 3.0)))
        self.n = int(math.ceil(float(ckt.num_muls) / self.m))
        # effective N
        self.N = self.m * self.n
        assert self.N >= ckt.num_muls

        # now select n', m1', m2'
        self.nP = int(math.ceil(math.sqrt(7.0 * self.m)))
        self.m1P = int(math.ceil(3.0 * self.m / self.nP))
        self.m2P = int(math.ceil((4.0 * self.m + 2.0) / self.nP))
        assert self.nP * self.m1P >= 3 * self.m
        assert self.nP * self.m2P >= 4 * self.m + 2

    def compute_y_w_vals(self, y, do_K):
        self.y = y
        self.yInv = util.invert_modp(y, Defs.prime)

        self.Yvec = _compute_powers(y, y, self.m)
        YIvec = _compute_powers(self.yInv, self.yInv, self.m)
        self.Ypvec = _compute_powers(self.Yvec[-1], self.Yvec[-1], self.n)

        yM = (self.Yvec[-1] * self.Ypvec[-1] * y) % Defs.prime
        Yqvec = _compute_powers(yM, y, self.Q)

        self.wai = _compute_wia(self.ckt.waq, Yqvec, YIvec, self.n, self.m)
        self.wbi = _compute_wib(self.ckt.wbq, Yqvec, self.n, self.m)
        self.wci = _compute_wic(self.ckt.wcq, Yqvec, self.Ypvec, self.Yvec, self.n, self.m)
        if do_K:
            self.K = sum( y * k % Defs.prime for (y, k) in izip(Yqvec, self.Kq) ) % Defs.prime

    def compute_x_vals(self, x):
        self.x = x
        xInv = util.invert_modp(x, Defs.prime)
        xn = pow(x, self.nP, Defs.prime)
        xnInv = pow(xInv, self.nP, Defs.prime)

        # powers of X for the polycommit
        self.Zvec_neg = _compute_powers(xnInv, xnInv, self.m1P)
        self.Zvec_pos = _compute_powers(x, xn, self.m2P)
        self.Zvec_last = ((x * x) % Defs.prime,)

        # powers of X for evaluating R and S
        self.Xpows_neg = _compute_powers(xInv, xInv, self.m)
        self.Xpows_pos = _compute_powers(x, x, self.m)

class BCCGPSqrtProver(_BCCGPSqrt):
    ai = None
    bi = None
    ci = None
    Dvec = None
    alpha_i = None
    beta_i = None
    gamma_i = None
    delta = None
    tx0 = None
    txi = None
    rx = None
    txi_save = None
    Uvec = None
    tauP = None
    tauPP = None
    tauU = None

    def __init__(self, ckt, curve=None):
        super(BCCGPSqrtProver, self).__init__(ckt, curve)
        pylaurent.init(str(Defs.prime))

    def witness_commit(self, ai, bi, ci):
        # pad and split
        ai += [0] * (self.N - len(ai))
        bi += [0] * (self.N - len(bi))
        ci += [0] * (self.N - len(ci))
        self.ai = [ ai[mval*self.n:(mval+1)*self.n] for mval in xrange(self.m) ]
        del ai
        self.bi = [ bi[mval*self.n:(mval+1)*self.n] for mval in xrange(self.m) ]
        del bi
        self.ci = [ ci[mval*self.n:(mval+1)*self.n] for mval in xrange(self.m) ]
        del ci

        self.alpha_i = [ self.gops.rand_scalar() for _ in xrange(self.m) ]
        self.beta_i = [ self.gops.rand_scalar() for _ in xrange(self.m) ]
        self.gamma_i = [ self.gops.rand_scalar() for _ in xrange(self.m) ]
        self.delta = self.gops.rand_scalar()
        self.Dvec = [ self.gops.rand_scalar() for _ in xrange(self.n) ]

        com_Ai = [ self.gops.pow_gih(x, y, 0) for (x, y) in izip(self.ai, self.alpha_i) ]
        com_Bi = [ self.gops.pow_gih(x, y, 0) for (x, y) in izip(self.bi, self.beta_i) ]
        com_Ci = [ self.gops.pow_gih(x, y, 0) for (x, y) in izip(self.ci, self.gamma_i) ]
        com_D = self.gops.pow_gih(self.Dvec, self.delta, 0)

        return (com_Ai, com_Bi, com_Ci, com_D)

    def _compute_laurent(self):
        # build representations of the polynomials
        zVec = [0] * self.n
        rx = [zVec] * (4 * self.m + 2)
        sx = [zVec] * (4 * self.m + 2)
        for i in xrange(self.m):
            rx[self.m + i] = self.bi[self.m - 1 - i]
            rx[2*self.m + i + 1] = self.ai[i]
            rx[3*self.m + i + 1] = self.ci[i]
            rx[4*self.m + 1] = self.Dvec
            sx[i] = self.wci[self.m - 1 - i]
            sx[self.m + i] = self.wai[self.m - 1 - i]
            sx[2*self.m + i + 1] = self.wbi[i]

        # call the laurent computation function from NTL
        tx = pylaurent.compute(self.Ypvec, rx, sx)
        # save r(x) for later
        self.rx = rx[self.m:2*self.m] + rx[2*self.m+1:]

        assert len(tx) == 8 * self.m + 3
        assert all(( t == 0 for t in tx[:self.m] ))

        tx_neg = [0] * (self.nP * self.m1P - 3 * self.m) + tx[self.m:4*self.m]
        tx_pos = tx[4*self.m+1:] + [0] * (self.nP * self.m2P - (4 * self.m + 2))

        self.tx0 = tx[4*self.m]
        self.txi = [ tx_neg[j*self.nP:(j+1)*self.nP] for j in xrange(self.m1P) ] + [ tx_pos[j*self.nP:(j+1)*self.nP] for j in xrange(self.m2P) ]

    def poly_commit(self, y):
        # compute wai, wbi, wci
        self.compute_y_w_vals(y, False)
        # compute ai * y^i
        for (ai, yi) in izip(self.ai, self.Yvec):
            for nidx in xrange(self.n):
                ai[nidx] *= yi
                ai[nidx] %= Defs.prime
        # compute t(x)
        self._compute_laurent()
        self.ai = None
        self.bi = None
        self.ci = None

        # choose blinder row and commitment randomness
        self.Uvec = [ self.gops.rand_scalar() for _ in xrange(self.nP - 1) ] + [0]
        self.tauP = [ self.gops.rand_scalar() for _ in xrange(self.m1P) ]
        self.tauPP = [ self.gops.rand_scalar() for _ in xrange(self.m2P) ]
        self.tauU = self.gops.rand_scalar()

        # blind and commit
        self.txi_save = self.txi[self.m1P]
        self.txi[self.m1P] = [ (t - u) % Defs.prime for (t, u) in izip(self.txi[self.m1P], chain((0,), self.Uvec)) ]
        com_TiP = [ self.gops.pow_gih(x, y, 0) for (x, y) in izip(self.txi[:self.m1P], self.tauP) ]
        com_TiPP = [ self.gops.pow_gih(x, y, 0) for (x, y) in izip(self.txi[self.m1P:], self.tauPP) ]
        self.txi.append(self.Uvec)
        com_U = self.gops.pow_gih(self.Uvec, self.tauU, 0)

        return (com_TiP, com_TiPP, com_U)

    def poly_eval(self, x):
        self.compute_x_vals(x)

        # first, compute vector-matrix product Z T
        Zvec = chain(reversed(self.Zvec_neg), self.Zvec_pos, self.Zvec_last)
        make_generator = lambda j, z: ( (z * self.txi[j][i]) % Defs.prime for i in xrange(self.nP) )
        gens = [ make_generator(j, z) for (j, z) in enumerate(Zvec) ]
        tbar = [ sum( g.next() for g in gens ) % Defs.prime for _ in xrange(self.nP) ]

        # then compute dot product Z tau
        # need to redefine Zvec because the iterator got used above
        Zvec = chain(reversed(self.Zvec_neg), self.Zvec_pos, self.Zvec_last)
        Tvec = chain(self.tauP, self.tauPP, (self.tauU,))
        taubar = sum( z * t for (z, t) in izip(Zvec, Tvec) ) % Defs.prime

        # now evaluate r
        Xmpows = [ (self.Xpows_pos[-1] * xval) % Defs.prime for xval in self.Xpows_pos ]    # x^m+1, x^m+2, ..., x^2m
        Xdpow = (Xmpows[-1] * x) % Defs.prime                                               # x^2m + 1

        # evaluate r
        Xpows = chain(reversed(self.Xpows_neg), self.Xpows_pos, Xmpows, (Xdpow,))
        make_generator = lambda j, xv: ( (xv * self.rx[j][i]) % Defs.prime for i in xrange(self.n) )
        gens = [ make_generator(j, x) for (j, x) in enumerate(Xpows) ]
        rEval = [ sum( g.next() for g in gens ) % Defs.prime for _ in xrange(self.n) ]

        # evaluate rho
        XYpows = ( (xv * yv) % Defs.prime for (xv, yv) in izip(self.Xpows_pos, self.Yvec) )
        Xpows = chain(self.Xpows_neg, XYpows, Xmpows, (Xdpow,))
        Rhovals = chain(self.beta_i, self.alpha_i, self.gamma_i, (self.delta,))
        rhoEval = sum( (rhoval * xval) % Defs.prime for (rhoval, xval) in izip(Rhovals, Xpows) ) % Defs.prime

        return (tbar, taubar, rEval, rhoEval)

class BCCGPSqrtProverNI(BCCGPSqrtProver):
    def __init__(self, ckt, curve=None):
        super(BCCGPSqrtProverNI, self).__init__(ckt, curve)
        self.fs = FiatShamir(Defs.prime)

    def run(self, inputs):
        # solve the AC
        (inputs, outputs, ai, bi, ci) = ACSolver(self.ckt).solve(inputs)

        # put the inputs and outputs into the transcript
        self.fs.put(inputs, True)
        self.fs.put(outputs, True)

        # commit to the witness
        wcom = self.witness_commit(ai, bi, ci)
        self.fs.put(wcom)

        # commit to the resulting polynomial
        chal = self.fs.rand_scalar()
        pcom = self.poly_commit(chal)
        self.fs.put(pcom)

        # evaluate the polynomial at the challenge point
        chal = self.fs.rand_scalar()
        peval = self.poly_eval(chal)
        self.fs.put(peval)

        # done!
        return self.fs.to_string()

class BCCGPSqrtVerifier(_BCCGPSqrt):
    com_Ai = None
    com_Bi = None
    com_Ci = None
    com_D = None
    com_TiP = None
    com_TiPP = None
    com_U = None
    x = None
    sx2 = None
    tbar = None
    taubar = None
    rEval = None
    rhoEval = None

    def witness_commit(self, (com_Ai, com_Bi, com_Ci, com_D)):
        self.com_Ai = com_Ai
        self.com_Bi = com_Bi
        self.com_Ci = com_Ci
        self.com_D = com_D

    def set_y(self, y):
        # we'll need these later to evaluate s(x)
        self.compute_y_w_vals(y, True)

    def poly_commit(self, (com_TiP, com_TiPP, com_U)):
        self.com_TiP = com_TiP
        self.com_TiPP = com_TiPP
        self.com_U = com_U

    def set_x(self, x):
        self.compute_x_vals(x)

        # generators for evaluating S(x)
        Xmpows_neg = ( (self.Xpows_neg[-1] * xval) % Defs.prime for xval in self.Xpows_neg )
        Xpows = chain(self.Xpows_neg, self.Xpows_pos, Xmpows_neg)
        Wvals = chain(self.wai, self.wbi, self.wci)

        # matrix-vector product
        make_generator = lambda wx, xval: ( (xval * wx[i]) % Defs.prime for i in range(self.n) )
        gens = [ make_generator(wx, xval) for (wx, xval) in izip(Wvals, Xpows) ]
        self.sx2 = [ (2 * sum( g.next() for g in gens )) % Defs.prime for _ in xrange(self.n) ] # 2 s(x)

    def poly_verify(self, (tbar, taubar, rEval, rhoEval)):
        self.tbar = tbar
        self.taubar = taubar
        self.rEval = rEval
        self.rhoEval = rhoEval

        # first, check that the opening is consistent with the commitments
        lhs1 = self.gops.pow_gih(self.tbar, self.taubar, 0)
        points_gen = chain(self.com_TiP, self.com_TiPP, (self.com_U,))
        scalars_gen = chain(reversed(self.Zvec_neg), self.Zvec_pos, self.Zvec_last)
        rhs1 = self.gops.multiexp(points_gen, scalars_gen, self.m1P + self.m2P + 1)
        if lhs1 != rhs1:
            raise ValueError('opening tbar,taubar is inconsistent with commitments')

        # now evaluate the committed polynomial
        assert self.n > self.m, 'n should be greater than m!'
        extrapows = _generate_powers(self.Xpows_pos[-1], self.x, self.n - self.m - 1)
        Xvec = chain((1,), self.Xpows_pos, extrapows)
        vEval = sum( (xval * tval) % Defs.prime for (xval, tval) in izip(Xvec, self.tbar) ) % Defs.prime

        # now compute r' * r - 2K and check against above poly evaluation
        rPrime = ( (r * y + s) % Defs.prime for (r, y, s) in izip(self.rEval, self.Ypvec, self.sx2) )
        tEval2K = sum( (rP * r) % Defs.prime for (rP, r) in izip(rPrime, self.rEval) ) % Defs.prime
        if tEval2K != (vEval + 2 * self.K) % Defs.prime:
            raise ValueError('t(x) inconsistent with v')

        # finally, check consistency of r with original commitments
        lhs2 = self.gops.pow_gih(self.rEval, self.rhoEval, 0)
        points_gen = chain(self.com_Ai, self.com_Bi, self.com_Ci, (self.com_D,))
        XYpows = ( (xv * yv) % Defs.prime for (xv, yv) in izip(self.Xpows_pos, self.Yvec) )
        Xmpows = ( (self.Xpows_pos[-1] * xv) % Defs.prime for xv in self.Xpows_pos )    # x^m+1, x^m+2, ..., x^2m
        Xdpow = (((self.Xpows_pos[-1] * self.Xpows_pos[-1]) % Defs.prime) * self.x) % Defs.prime
        scalars_gen = chain(XYpows, self.Xpows_neg, Xmpows, (Xdpow,))
        rhs2 = self.gops.multiexp(points_gen, scalars_gen, 3 * self.m + 1)
        if lhs2 != rhs2:
            raise ValueError('r inconsistent with initial commits')

class BCCGPSqrtVerifierNI(BCCGPSqrtVerifier):
    fs = None

    def run(self, pf):
        self.fs = FiatShamir.from_string(pf)
        assert Defs.prime == self.fs.q

        # handle inputs and outputs
        inputs = self.fs.take(True)
        outputs = self.fs.take(True)
        self.set_io(inputs, outputs)

        # handle witness commit
        wcom = self.fs.take()[0]
        self.witness_commit(wcom)

        # first challenge and polycommit
        chal = self.fs.rand_scalar()
        pcom = self.fs.take()[0]
        self.set_y(chal)
        self.poly_commit(pcom)

        # poly verification
        chal = self.fs.rand_scalar()
        peval = self.fs.take()[0]
        self.set_x(chal)
        self.poly_verify(peval)
