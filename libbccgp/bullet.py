#!/usr/bin/python
#
# (C) Riad S. Wahby <rsw@cs.stanford.edu>
#
# Bulletproofs implementation

from itertools import chain, izip, repeat

from libbccgp.bccgp import _BCCGPBase, _compute_powers, _compute_sparse_vec_mat
from libbccgp.solve import ACSolver

from libfennel.defs import Defs
from libfennel.fiatshamir import FiatShamir
import libfennel.util as util

def _eval_poly(p, x):
    ret = p[-1]
    for pi in reversed(p[:-1]):
        for idx in xrange(len(ret)):
            ret[idx] = (ret[idx] * x + pi[idx]) % Defs.prime
    return ret

class _BulletBase(_BCCGPBase):
    y = None
    yInv = None
    z = None
    Ypows = None
    YIpows = None
    ZWL = None
    yIZWR = None
    ZWO = None

    def compute_y_z_w_vals(self, y, z, do_K):
        self.y = y
        self.yInv = util.invert_modp(y, Defs.prime)
        self.z = z

        Zpows = _compute_powers(z, z, self.Q)
        Ypows = _compute_powers(1, self.y, self.n)
        self.YIpows = _compute_powers(1, self.yInv, self.n)

        # compute matrix-vector products
        wvec = _compute_sparse_vec_mat(self.ckt.waq, Zpows)     # Zpows * WL
        self.ZWL = [ wvec.get(idx, 0) % Defs.prime for idx in xrange(self.n) ]

        wvec = _compute_sparse_vec_mat(self.ckt.wbq, Zpows)     # Zpows * WR
        self.yIZWR = [ (yv * wvec.get(idx, 0)) % Defs.prime for (idx, yv) in enumerate(self.YIpows) ]

        wvec = _compute_sparse_vec_mat(self.ckt.wcq, Zpows)     # Zpows * WO
        self.ZWO = [ wvec.get(idx, 0) % Defs.prime for idx in xrange(self.n) ]

        if do_K:
            # compute k(y,z) + Zpows * c, where c is Kq in BCCGP notation
            kyzgen = sum( (rv * lv) for (lv, rv) in izip(self.ZWL, self.yIZWR) ) % Defs.prime
            zcgen = sum( (zv * kv) for (zv, kv) in izip(Zpows, self.Kq) ) % Defs.prime
            self.K = kyzgen + zcgen
        else:
            self.Ypows = Ypows      # Prover needs this, Verifier doesn't

    def extend_yipows(self):
        nExtra = self.n - len(self.YIpows)
        # need to call this when we start the inner product argument
        self.YIpows += _compute_powers((self.YIpows[-1] * self.yInv) % Defs.prime, self.yInv, nExtra)
        assert len(self.YIpows) == self.n

class BulletProver(_BulletBase):
    aL = None
    aR = None
    aO = None
    alpha = None
    beta = None
    rho = None
    sL = None
    sR = None
    lx = None
    rx = None
    tx = None
    taui = None
    lEv = None
    rEv = None
    gV = None
    hV = None
    u = None

    def witness_commit(self, aL, aR, aO):
        self.aL = aL
        self.aR = aR
        self.aO = aO

        # generate all the randomness
        self.alpha = self.gops.rand_scalar()
        self.beta = self.gops.rand_scalar()
        self.rho = self.gops.rand_scalar()
        self.sL = [ self.gops.rand_scalar() for _ in xrange(self.n) ]
        self.sR = [ self.gops.rand_scalar() for _ in xrange(self.n) ]

        # now commit to the witness
        nRnd = 2 ** util.clog2(self.n)
        com_AI = self.gops.pow_gih(chain(aL, repeat(0, nRnd - self.n), aR), self.alpha, 0, nRnd + self.n)
        com_AO = self.gops.pow_gih(aO, self.beta, 0, self.n)
        com_S = self.gops.pow_gih(chain(self.sL, repeat(0, nRnd - self.n), self.sR), self.rho, 0, nRnd + self.n)

        return (com_AI, com_AO, com_S)

    def poly_commit(self, y, z):
        self.compute_y_z_w_vals(y, z, False)

        # compute l(X)
        zvec = [0] * self.n
        for (idx, rv) in enumerate(self.yIZWR):
            self.aL[idx] = (rv + self.aL[idx]) % Defs.prime
        self.lx = [ zvec, self.aL, self.aO, self.sL ]

        # compute r(X)
        for (idx, (yv, lv)) in enumerate(izip(self.Ypows, self.ZWL)):
            self.ZWO[idx] = (self.ZWO[idx] - yv) % Defs.prime
            self.aR[idx] = (self.aR[idx] * yv + lv) % Defs.prime
            self.sR[idx] = (self.sR[idx] * yv) % Defs.prime
        self.rx = [ self.ZWO, self.aR, zvec, self.sR ]

        # don't need these variables any more
        self.aL = self.aR = self.aO = self.sL = self.sR = self.yIZWR = self.ZWL = self.ZWO = None

        # now compute all coeffs of tx except T0 (which is 0) and T2 (which V reconstructs for itself)
        # in BCCGP, this is done using polynomial multiplication, but that doesn't make sense here
        # because the degree of each polynomial to be multiplied is very small (4)
        Ti = [0] * 6
        for lidx in xrange(4):
            for ridx in xrange(4):
                oidx = lidx + ridx
                if oidx == 0 or oidx == 2:
                    continue
                tval = sum( (lv * rv) % Defs.prime for (lv, rv) in izip(self.lx[lidx], self.rx[ridx]) )
                Ti[oidx-1] = (Ti[oidx-1] + tval) % Defs.prime

        # commit to all coeffs of tx except T2
        self.tx = [Ti[0], Ti[2], Ti[3], Ti[4], Ti[5]]
        self.taui = [ self.gops.rand_scalar() for _ in xrange(5) ]
        com_Ti = [ self.gops.pow_gh(tv, tauv) for (tv, tauv) in izip(self.tx, self.taui) ]

        return com_Ti

    def poly_eval(self, x):
        # evaluate l(x) and r(x)
        self.lEv = _eval_poly(self.lx, x)
        self.rEv = _eval_poly(self.rx, x)

        # don't need l(x) and r(x) any more
        self.lx = self.rx = None

        tEval = sum( (lv * rv) % Defs.prime for (lv, rv) in izip(self.lEv, self.rEv) ) % Defs.prime
        taux = util.horner_eval([0, self.taui[0], 0, self.taui[1], self.taui[2], self.taui[3], self.taui[4]], x)
        mu = util.horner_eval([0, self.alpha, self.beta, self.rho], x)

        return (taux, mu, tEval)

    def iparg_init(self, xIP=None):
        if xIP is not None:
            self.u = (self.gops.pow_g(xIP),)
            # pad out n, l, and r
            nExtra = 2 ** util.clog2(self.n) - self.n
            self.n += nExtra
            self.lEv += [0] * nExtra
            self.rEv += [0] * nExtra
            if nExtra != 0:
                self.extend_yipows()

        nP = self.n // 2
        cL = sum( (lv * rv) % Defs.prime for (lv, rv) in izip(self.lEv[:nP], self.rEv[nP:]) ) % Defs.prime
        cR = sum( (lv * rv) % Defs.prime for (lv, rv) in izip(self.lEv[nP:], self.rEv[:nP]) ) % Defs.prime

        if xIP is not None:
            # for initial messages we have to be slightly careful because we have h, not h'
            h_pows_1 = ( (rv * iv) % Defs.prime for (rv, iv) in izip(self.rEv[nP:], self.YIpows[:nP]) )
            L1 = self.gops.pow_gi(chain(self.lEv[:nP], h_pows_1), nP, 1, self.n)
            L = self.gops.exp_mul(self.u[0], cL, L1)

            h_pows_2 = ( (rv * iv) % Defs.prime for (rv, iv) in izip(self.rEv[:nP], self.YIpows[nP:]) )
            R1 = self.gops.pow_gi(self.lEv[nP:], 0)
            R2 = self.gops.pow_gi(h_pows_2, self.n + nP, 1, nP)
            R = self.gops.exp_mul(self.u[0], cR, self.gops.mul(R1, R2))
        else:
            # otherwise, we have the bases computed already
            L = self.gops.multiexp(chain(self.gV[nP:], self.hV[:nP], self.u), chain(self.lEv[:nP], self.rEv[nP:], (cL,)), self.n + 1)
            R = self.gops.multiexp(chain(self.gV[:nP], self.hV[nP:], self.u), chain(self.lEv[nP:], self.rEv[:nP], (cR,)), self.n + 1)

        return (L, R)

    def iparg_cont(self, chal):
        nP = self.n // 2
        cInv = util.invert_modp(chal, Defs.prime)
        if self.gV is None:
            self.gV = [ self.gops.pow_gij(idx, nP + idx, cInv, chal) for idx in xrange(nP) ]
            h1g = ( (chal * iv) % Defs.prime for iv in self.YIpows[:nP] )
            h2g = ( (cInv * iv) % Defs.prime for iv in self.YIpows[nP:] )
            self.hV = [ self.gops.pow_gij(self.n + idx, self.n + nP + idx, h1g.next(), h2g.next()) for idx in xrange(nP) ]
        else:
            self.gV = [ self.gops.multiexp([self.gV[idx], self.gV[idx + nP]], [cInv, chal]) for idx in xrange(nP) ]
            self.hV = [ self.gops.multiexp([self.hV[idx], self.hV[idx + nP]], [chal, cInv]) for idx in xrange(nP) ]

        self.lEv = [ (al * chal + ar * cInv) % Defs.prime for (al, ar) in izip(self.lEv[:nP], self.lEv[nP:]) ]
        self.rEv = [ (bl * cInv + br * chal) % Defs.prime for (bl, br) in izip(self.rEv[:nP], self.rEv[nP:]) ]

        self.n = nP
        if self.n > 1:
            return True
        return False

    def iparg_fin(self):
        assert self.n == 1, 'called iparg_fin too early'
        return (self.lEv[0], self.rEv[0])

class BulletProverNI(BulletProver):
    def __init__(self, ckt, curve=None):
        super(BulletProverNI, self).__init__(ckt, curve)
        self.fs = FiatShamir(Defs.prime)

    def run(self, inputs):
        # solve the AC
        (inputs, outputs, ai, bi, ci) = ACSolver(self.ckt).solve(inputs)

        # put inputs and outputs into the transcript
        self.fs.put(inputs, True)
        self.fs.put(outputs, True)

        # commit to the witness
        wcom = self.witness_commit(ai, bi, ci)
        self.fs.put(wcom)

        # commit to the resulting polynomial
        chal_y = self.fs.rand_scalar()
        chal_z = self.fs.rand_scalar()
        pcom = self.poly_commit(chal_y, chal_z)
        self.fs.put(pcom)

        # evaluate the polynomial at the challenge point
        chal = self.fs.rand_scalar()
        peval = self.poly_eval(chal)
        self.fs.put(peval)

        # now run recursive argument until we bottom out
        chal = self.fs.rand_scalar()
        lrval = self.iparg_init(chal)
        self.fs.put(lrval)
        while self.iparg_cont(self.fs.rand_scalar()):
            lrval = self.iparg_init(None)
            self.fs.put(lrval)

        # finally, the last value
        abvals = self.iparg_fin()
        self.fs.put(abvals)

        # done!
        return self.fs.to_string()

class BulletVerifier(_BulletBase):
    com_AI = None
    com_AO = None
    com_S = None
    com_Ti = None
    P = None
    x = None
    xIP = None
    LRvals = None
    cvals = None
    nbits = None
    Xpows = None

    def witness_commit(self, (com_AI, com_AO, com_S)):
        self.com_AI = com_AI
        self.com_AO = com_AO
        self.com_S = com_S

    def set_y_z(self, y, z):
        self.compute_y_z_w_vals(y, z, True)

    def poly_commit(self, com_Ti):
        self.com_Ti = com_Ti

    def set_x(self, x):
        self.x = x

    def poly_verify_init(self, (taux, mu, tEval), xIP):
        # we'll need these
        x = self.x
        Xpows = _compute_powers(1, x, 7)
        x2 = Xpows[2]

        # first, check that claimed evaluation satisfies AC
        lhs = self.gops.pow_gh(tEval, taux)
        Xpows[2] = (x2 * self.K) % Defs.prime
        rhs = self.gops.multiexp([self.com_Ti[0], self.gops.g] + self.com_Ti[1:], Xpows[1:])
        if lhs != rhs:
            raise ValueError('AC satisfiability check failed')

        # now we're ready to compute the powers of g and h and then to compute P
        # first, let's do powers of g, which is just WR^x = x * yIZWR
        pow_g = ( (x * yv) % Defs.prime for yv in self.yIZWR )
        # For h', we have x * ZWL + ZWO - Ypows, where h' = h ^ YIpows
        # thus, to the base h we have (x * ZWL + ZWO - Ypows) * YIpows = (x * ZWL + ZWO) * YIpows - 1
        comp_h = lambda lv, ov, iv: ((((x * lv) % Defs.prime) + ov) * iv - 1) % Defs.prime
        pow_h = ( comp_h(lv, ov, iv) for (lv, ov, iv) in izip(self.ZWL, self.ZWO, self.YIpows) )

        # we're going to run an inner-product argument on
        # g_vec, h'_vec, g, P h^-mu, t
        # to use Bulletproofs Protocol #1, we convert this statement to
        # g_vec, h'_vec, g^xIP, P h^-mu g^(xIP t)

        # here, we only compute part of P h^-mu g^(xIP t); we wait to compute the rest until the very end
        nRnd = 2 ** util.clog2(self.n)
        self.P = self.gops.pow_gih(chain(pow_g, repeat(0, nRnd - self.n), pow_h), Defs.prime - mu, 0, nRnd + self.n)

        # get ready for inner product arg
        Xpows[2] = x2
        Xpows[4] = (tEval * xIP) % Defs.prime
        self.Xpows = Xpows[:5]
        self.xIP = xIP
        self.cvals = []
        self.LRvals = []
        self.nbits = util.clog2(self.n)
        if self.n != 2 ** self.nbits:
            self.n = 2 ** self.nbits
            self.extend_yipows()

    def iparg_cont(self, chal, LRval):
        self.cvals.append(chal)
        self.LRvals.extend(LRval)

        return self.nbits != len(self.cvals)

    def iparg_fin(self, (a, b)):
        # compute inverses mod p
        cprod = reduce(lambda x, y: (x * y) % Defs.prime, self.cvals)
        cprodinv = util.invert_modp(cprod, Defs.prime)
        cinvs = [0] * len(self.cvals)
        for idx in xrange(len(self.cvals)):
            cvs = chain(self.cvals[:idx], self.cvals[idx+1:])
            cinvs[idx] = reduce(lambda x, y: (x * y) % Defs.prime, cvs, cprodinv)

        csqs = [ (cval * cval) % Defs.prime for cval in self.cvals ]
        cinvsqs = [ (cval * cval) % Defs.prime for cval in cinvs ]
        # compute powers for multiexps
        gpows = [cprodinv]
        for cval in csqs:
            new = [0] * 2 * len(gpows)
            for (idx, gpow) in enumerate(gpows):
                new[2*idx] = gpow
                new[2*idx+1] = (gpow * cval) % Defs.prime
            gpows = new

        # compute final value of P = Lx^2 P Rx^-2 (iterated), via multiexp
        ppoints = chain((self.P, self.com_AI, self.com_AO, self.com_S, self.gops.g), self.LRvals)
        pscalars = chain(self.Xpows, chain.from_iterable(izip(csqs, cinvsqs)))
        lhs = self.gops.multiexp(ppoints, pscalars, len(self.LRvals) + 5)

        # compute final g and h with one multiexp each
        assert len(gpows) == self.n, 'wrong gpows length'
        g_fin = self.gops.pow_gi(gpows, 0, 1, self.n)
        hpows = ( (iv * pv) % Defs.prime for (iv, pv) in izip(self.YIpows, reversed(gpows)) )
        h_fin = self.gops.pow_gi(hpows, self.n, 1, self.n)
        # then check the final equality
        rhs = self.gops.multiexp([g_fin, h_fin, self.gops.g], [a, b, (((a*b) % Defs.prime) * self.xIP) % Defs.prime])

        if lhs != rhs:
            raise ValueError('inner product argument failed')

class BulletVerifierNI(BulletVerifier):
    fs = None

    def run(self, pf):
        self.fs = FiatShamir.from_string(pf)
        assert Defs.prime == self.fs.q

        # handle inputs and outputs
        inputs = self.fs.take(True)
        outputs = self.fs.take(True)
        self.set_io(inputs, outputs)

        # get the witness
        wcom = self.fs.take()[0]
        self.witness_commit(wcom)

        # get the polycommit
        chal_y = self.fs.rand_scalar()
        chal_z = self.fs.rand_scalar()
        self.set_y_z(chal_y, chal_z)
        pcom = self.fs.take()
        self.poly_commit(pcom)

        # get the polyeval
        chal = self.fs.rand_scalar()
        self.set_x(chal)
        peval = self.fs.take()[0]

        # run the recursive argument
        chal = self.fs.rand_scalar()
        self.poly_verify_init(peval, chal)
        cont = True
        while cont:
            lrval = self.fs.take()[0]
            chal = self.fs.rand_scalar()
            cont = self.iparg_cont(chal, lrval)

        # finally, check the result of the recursive argument
        abvals = self.fs.take()[0]
        self.iparg_fin(abvals)
