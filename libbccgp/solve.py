#!/usr/bin/python
#
# (C) 2018 Riad S. Wahby <rsw@cs.stanford.edu>
#
# produce a satisfying assignment to an AC

from collections import deque
from itertools import izip
import sys

from libbccgp.pws import Input, Output, Mul, pws_to_constraints
from libfennel.defs import Defs

class ACSolver(object):
    def __init__(self, acrepr):
        self.acrepr = acrepr
        self.nondet_gen = lambda inputs: inputs
        #self.get_default = lambda _: 0
        self.get_default = lambda _: Defs.gen_random()

    def set_nondet_gen(self, fn):
        self.nondet_gen = fn

    def solve(self, inputs, check_extra=False):
        acrepr = self.acrepr
        # get all the inputs ready
        inputs = self.nondet_gen(inputs)

        # now set all of the inputs
        queue = deque(acrepr.gates(Input))
        for gateNum in queue:
            gate = acrepr.wires[gateNum]
            gate.set_input(inputs.setdefault(gate.innum, self.get_default(gate.innum)), None)

        # propagate forward
        while queue:
            gateNum = queue.popleft()
            gate = acrepr.wires[gateNum]
            for succNum in acrepr.whatuses[gateNum]:
                succ = acrepr.wires[succNum]
                if succ.set_input(gate.output, gateNum):
                    queue.append(succNum)

        # gather outputs
        outputs = {}
        for gateNum in acrepr.gates(Output):
            gate = acrepr.wires[gateNum]
            outputs[gate.num] = gate.output
            assert gate.output is not None

        # gather satisfying assignment
        ai = [None] * acrepr.num_muls
        bi = [None] * acrepr.num_muls
        ci = [None] * acrepr.num_muls
        for gateNum in acrepr.gates(Mul):
            gate = acrepr.wires[gateNum]
            assert gate.inL is not None and gate.inR is not None and gate.output is not None
            ai[gate.label] = gate.inL
            bi[gate.label] = gate.inR
            ci[gate.label] = gate.output

        # put private inputs in the satisfying assignment
        for label in acrepr.priv_input_map:
            inp = inputs.setdefault(label, self.get_default(label))
            (is_b, priv_in) = acrepr.priv_input_map[label]
            if priv_in < acrepr.dummy_start:
                continue
            if is_b:
                bi[priv_in] = inp
            else:
                ai[priv_in] = inp

        # finally, compute correct values for any dummy multipliers
        if bi[-1] is None:
            # this could be none if we only needed an odd number of dummies
            bi[-1] = 0
        for dNum in xrange(acrepr.dummy_start, acrepr.num_muls):
            ci[dNum] = (ai[dNum] * bi[dNum]) % Defs.prime

        inputs = {k:v for (k,v) in inputs.items() if k in acrepr.public_inputs}

        if check_extra:
            assert all( a is not None for a in ai )
            assert all( b is not None for b in bi )
            assert all( c is not None for c in ci )
            assert all( (a * b) % Defs.prime == c for (a, b, c) in izip(ai, bi, ci) )
            Q = len(acrepr.kq)
            Kq = [0] * Q
            for (idx, kqcoeffs) in enumerate(acrepr.kq):
                kqval = 0
                for (ionum, coeff) in kqcoeffs.iteritems():
                    if ionum < 0:
                        ionum = -1 - ionum
                        kqval += coeff * outputs[ionum]
                    elif ionum > 0:
                        ionum -= 1
                        kqval += coeff * inputs[ionum]
                    else:
                        kqval += coeff
                Kq[idx] = kqval % Defs.prime

            for (idx, (aq, bq, cq)) in enumerate(izip(acrepr.waq, acrepr.wbq, acrepr.wcq)):
                av = bv = cv = 0
                for aidx in aq:
                    av += aq[aidx] * ai[aidx]
                for bidx in bq:
                    bv += bq[bidx] * bi[bidx]
                for cidx in cq:
                    cv += cq[cidx] * ci[cidx]
                tot = (av + bv + cv) % Defs.prime
                if tot != Kq[idx]:
                    print "Error got %d %d %d = %d for constr %d" % (av, bv, cv, Kq[idx], idx)
                    print aq
                    print bq
                    print cq
                    print acrepr.kq[idx]
                    print Kq[idx]

        return (inputs, outputs, ai, bi, ci)

def main():
    if len(sys.argv) < 2:
        sys.exit("usage: " + sys.argv[0] + " <infile.pws> [<priv_input_numbers>]")
    elif len(sys.argv) < 3:
        pubins = [0]
    else:
        pubins = eval(sys.argv[2]) # pylint: disable=eval-used

    solver = ACSolver(pws_to_constraints(sys.argv[1], pubins, None))
    (inputs, outputs, ai, bi, ci) = solver.solve({})

    print inputs
    print outputs
    print ai
    print bi
    print ci

if __name__ == '__main__':
    main()
