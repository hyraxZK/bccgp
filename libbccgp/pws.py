#!/usr/bin/python
#
# convert a PWS file to the format necessary for BCCGP et al
#
# (C) 2018 Riad S. Wahby <rsw@cs.nyu.edu>

from collections import deque
import heapq
import re
import sys

from libfennel.defs import Defs

varOrConst = r"(?:V(\d+)|(-?\d+))"
copyPat = re.compile(r"P V(\d+) = %s E" % varOrConst)
gatePat = re.compile(r"P (O|V)(\d+) = %s ([^ ]+) %s E" % (varOrConst, varOrConst))
inPat = re.compile(r"P V(\d+) = I(\d+) E")
outPat = re.compile(r"P O(\d+) = V(\d+) E")

WMASK = (1 << 60) - 1
WOFFL =     2**60
WOFFR = 2 * 2**60
WOFF1 = 3 * 2**60
WOFF2 = 4 * 2**60
WOFF3 = 5 * 2**60
WOFF4 = 6 * 2**60
WOFF5 = 7 * 2**60

class Mul(object):
    reached = False
    label = -1
    constrs = None
    inL = None
    inR = None
    output = None

    def set_input(self, inp, fnum):
        if self.uses[0] == self.uses[1]:
            self.inL = inp
            self.inR = inp
            other = inp
        elif self.uses[0] == fnum:
            self.inL = inp
            other = self.inR
        else:
            self.inR = inp
            other = self.inL

        if other is None:
            return False

        self.output = (other * inp) % Defs.prime
        return True

    def __repr__(self):
        return "%8d: %d * %d (%d)" % (self.num, self.uses[0], self.uses[1], self.label)

    def __init__(self, acrepr, num, inL, inR):
        self.num = num
        self.uses = [inL, inR]
        acrepr.use(num, self.uses)

    def set_label(self, lab):
        self.label = lab

    def hash_repr(self):
        self.uses.sort()
        return ('*', self.uses[0], self.uses[1])

class Add(object):
    reached = False
    constrs = None
    inp_save = None
    output = None

    def set_input(self, inp, fnum):
        if self.uses[0] == self.uses[1]:
            self.inp_save = inp
        elif self.inp_save is None:
            self.inp_save = inp
            return False

        if self.neg:
            if self.uses[0] == fnum:
                output = inp - self.inp_save
            else:
                output = self.inp_save - inp
        else:
            output = self.inp_save + inp
        self.output = output % Defs.prime
        return True

    def __repr__(self):
        return "%8d: %d %s %d (%s)" % (self.num, self.uses[0], '-' if self.neg else '+', self.uses[1], str(self.constrs))

    def __init__(self, acrepr, num, inL, inR, neg):
        self.num = num
        self.uses = [inL, inR]
        self.neg = neg
        acrepr.use(num, self.uses)

    def hash_repr(self):
        if self.neg:
            return ('-', self.uses[0], self.uses[1])
        self.uses.sort()
        return ('+', self.uses[0], self.uses[1])

class ConstMul(object):
    reached = False
    constrs = None
    output = None

    def set_input(self, inp, _):
        self.output = (self.const * inp) % Defs.prime
        return True

    def __repr__(self):
        return "%8d: const(%d) * %d (%s)" % (self.num, self.const, self.uses[0], str(self.constrs))

    def __init__(self, acrepr, num, wire, const):
        self.num = num
        self.const = const
        self.uses = [wire]
        acrepr.use(num, self.uses)

    def hash_repr(self):
        return ('c*', self.const, self.uses[0])

class ConstAdd(object):
    reached = False
    constrs = None
    output = None

    def set_input(self, inp, _):
        if self.neg:
            output = self.const - inp
        else:
            output = self.const + inp
        self.output = output % Defs.prime
        return True

    def __repr__(self):
        return "%8d: const(%d) %s %d (%s)" % (self.num, self.const, '-' if self.neg else '+', self.uses[0], str(self.constrs))

    def __init__(self, acrepr, num, wire, const, neg):
        self.num = num
        self.const = const
        self.neg = neg
        self.uses = [wire]
        acrepr.use(num, self.uses)

    def hash_repr(self):
        if self.neg:
            return ('c-', self.const, self.uses[0])
        return ('c+', self.const, self.uses[0])

class Input(object):
    reached = False
    uses = []
    label = 0
    constrs = None
    output = None

    def set_input(self, inp, _):
        self.output = inp % Defs.prime
        return True

    def __repr__(self):
        return "%8d: in#%d (%d)" % (self.num, self.innum, self.label)

    def __init__(self, acrepr, num, innum):
        self.num = num
        self.innum = innum
        self.acrepr = acrepr

    def set_label(self, lab):
        self.label = lab
        self.acrepr.inputlabels[lab] = self.innum

    @staticmethod
    def hash_repr():
        return None

class Output(object):
    reached = False
    constrs = None
    output = None

    def set_input(self, inp, _):
        self.output = inp % Defs.prime
        return False

    def __repr__(self):
        return "%8d: out#%d (%s)" % (self.num, self.uses[0], str(self.constrs))

    def __init__(self, acrepr, num, wire):
        self.num = num
        self.uses = [wire]
        acrepr.use(num, self.uses)

    @staticmethod
    def hash_repr():
        return None

class Const(object):
    reached = False
    uses = []

    def __repr__(self):
        return "%8d: const(%d)" % (self.num, self.const)

    def __init__(self, num, const):
        self.num = num
        self.const = const

class Pass(object):
    reached = False

    def __repr__(self):
        return "%8d: pass(%d)" % (self.num, self.uses[0])

    def __init__(self, acrepr, num, wire):
        self.num = num
        self.uses = [wire]
        acrepr.use(num, self.uses)

class ACRepr(object):
    next_label = None               # label whose b_i is not yet allocated to a private input

    def __init__(self, posn_outs=False):
        self.wires = {}             # representation of what drives each wire
        self.whatuses = {}          # mapping from wire number to the gates it feeds (for fw-prop)
        self.inputlabels = {}       # label-to-input-number mapping
        self.num_muls = -1          # how many multipliers do we have?
        self.dummy_start = -1       # starting multiplier number for dummies
        self.public_inputs = []     # which inputs are public?
        self.priv_input_map = {}    # private input to label number mapping
        # constraints
        self.waq = []
        self.wbq = []
        self.wcq = []
        self.kq = []

        self.in_posn_curr = 0
        if posn_outs:
            self.out_posns = []
        else:
            self.out_posns = None

    def use(self, num, what):
        for w in what:
            self.whatuses.setdefault(w, set()).add(num)

    def __str__(self):
        return self.__repr__()

    def __repr__(self):
        ostrs = ["Wires: {"] + [ repr(self.wires[x]) for x in self.wires ]
        ostrs += ["}\n***", repr(self.whatuses), '***\nConstraints: [']
        ostrs += [ repr((a, b, c, k)) for (a, b, c, k) in zip(self.waq, self.wbq, self.wcq, self.kq) ]
        ostrs += [']', "num_muls = (%d,%d)" % (self.num_muls, self.dummy_start), repr(self.priv_input_map)]
        return '\n'.join(ostrs)

    def gates(self, ty):
        return [ x for x in self.wires if isinstance(self.wires[x], ty) ]

    def add_constr(self, constr):
        if constr is not None:
            assert len(constr) == 4
            #(waq, wbq, wcq, kq) = constr
            self.waq.append(constr[0])
            self.wbq.append(constr[1])
            self.wcq.append(constr[2])
            self.kq.append(constr[3])

def get_wirenum(acrepr, s, ignore_drive=False):
    wirenum = int(s)
    assert (wirenum & WMASK) == wirenum, "Got wire number >= 2^60, something is probably wrong"
    if not ignore_drive:
        assert wirenum not in acrepr.wires, "multiply-driven wire %s" % wirenum
    return wirenum

def parse(acrepr, fh, rdlrepr):
    if rdlrepr is not None:
        innum_to_wire = {}      # need this for wiring up RDL

    # step 1: read in PWS
    for line in fh:
        comStart = line.find('//')
        if comStart >= 0:
            line = line[:comStart]
        line = line.strip()
        # if the line is just empty or a comment, skip it
        if not line:
            continue

        #### normal gate
        m = gatePat.match(line)
        # 0 = whole line
        # 1 = O or V
        # 2 = gate number
        # 3 = left in wire number
        # 4 = left in const value
        # 5 = gate operation
        # 6 = right in wire number
        # 7 = right in const value
        if m is not None:
            # handle either wire-driving our output-driving gates, e.g., "O1 = V2 + V3" or "V1 = V2 + V3"
            basenum = get_wirenum(acrepr, m.group(2))
            if m.group(1) == 'O':
                wirenum = basenum + WOFF5
                acrepr.wires[basenum] = Output(acrepr, basenum, wirenum)
            else:
                wirenum = basenum

            # handle constants --- constant-prop will take care of optimizing
            if m.group(4) is not None:
                inL = basenum + WOFFL
                acrepr.wires[inL] = Const(inL, int(m.group(4)))
            else:
                inL = int(m.group(3))

            if m.group(7) is not None:
                inR = basenum + WOFFR
                acrepr.wires[inR] = Const(inR, int(m.group(7)))
            else:
                inR = int(m.group(6))

            # now handle the gate
            oper = m.group(5)
            if oper == '*':
                acrepr.wires[wirenum] = Mul(acrepr, wirenum, inL, inR)

            elif oper == '+':
                acrepr.wires[wirenum] = Add(acrepr, wirenum, inL, inR, False)

            elif oper == 'minus':
                acrepr.wires[wirenum] = Add(acrepr, wirenum, inL, inR, True)

            elif oper == 'OR':
                wirenum1 = basenum + WOFF1
                wirenum2 = basenum + WOFF2
                acrepr.wires[wirenum1] = Add(acrepr, wirenum1, inL, inR, False)             # L + R
                acrepr.wires[wirenum2] = Mul(acrepr, wirenum2, inL, inR)                    # L R
                acrepr.wires[wirenum] = Add(acrepr, wirenum, wirenum1, wirenum2, True)      # L + R - L R

            elif oper == 'XOR':
                wirenum1 = basenum + WOFF1
                wirenum2 = basenum + WOFF2
                wirenum3 = basenum + WOFF3
                acrepr.wires[wirenum1] = Add(acrepr, wirenum1, inL, inR, False)             # L + R
                acrepr.wires[wirenum2] = Mul(acrepr, wirenum2, inL, inR)                    # L R
                acrepr.wires[wirenum3] = ConstMul(acrepr, wirenum3, wirenum2, 2)            # 2 L R
                acrepr.wires[wirenum] = Add(acrepr, wirenum, wirenum1, wirenum3, True)      # L + R - 2 L R

            elif oper == 'NOT':
                acrepr.wires[wirenum] = ConstAdd(acrepr, wirenum, inL, 1, True)             # 1 - L

            elif oper == 'NAND':
                wirenum1 = basenum + WOFF1
                acrepr.wires[wirenum1] = Mul(acrepr, wirenum1, inL, inR)                    # L R
                acrepr.wires[wirenum] = ConstAdd(acrepr, wirenum, wirenum1, 1, True)        # 1 - L R

            elif oper == 'NOR':
                wirenum1 = basenum + WOFF1
                wirenum2 = basenum + WOFF2
                wirenum3 = basenum + WOFF3
                acrepr.wires[wirenum1] = Mul(acrepr, wirenum1, inL, inR)                    # L R
                acrepr.wires[wirenum2] = Add(acrepr, wirenum2, inL, inR, False)             # L + R
                acrepr.wires[wirenum3] = Add(acrepr, wirenum3, wirenum1, wirenum2, True)    # L R - (L + R)
                acrepr.wires[wirenum] = ConstAdd(acrepr, wirenum, wirenum3, 1, False)       # 1 + L R - (L + R)

            elif oper == 'NXOR':
                wirenum1 = basenum + WOFF1
                wirenum2 = basenum + WOFF2
                wirenum3 = basenum + WOFF3
                wirenum4 = basenum + WOFF4
                acrepr.wires[wirenum1] = Mul(acrepr, wirenum1, inL, inR)                    # L R
                acrepr.wires[wirenum2] = Add(acrepr, wirenum2, inL, inR, False)             # L + R
                acrepr.wires[wirenum3] = ConstMul(acrepr, wirenum3, wirenum1, 2)            # 2 L R
                acrepr.wires[wirenum4] = Add(acrepr, wirenum4, wirenum3, wirenum2, True)    # 2 L R - (L + R)
                acrepr.wires[wirenum] = ConstAdd(acrepr, wirenum, wirenum4, 1, False)       # 1 + 2 L R - (L + R)

            elif oper == 'NAAB':
                wirenum1 = basenum + WOFF1
                acrepr.wires[wirenum1] = Mul(acrepr, wirenum1, inL, inR)                    # L R
                acrepr.wires[wirenum] = Add(acrepr, wirenum, inR, wirenum1, True)           # R - L R

            elif oper == 'PASS':
                acrepr.wires[wirenum] = Pass(acrepr, wirenum, inL)                          # L

            else:
                raise ValueError("got unknown operator %s"  % m.group(0))

            continue

        #### copy or const gate
        m = copyPat.match(line)
        if m is not None:
            wirenum = get_wirenum(acrepr, m.group(1))

            if m.group(2) is not None:
                # pass gate
                acrepr.wires[wirenum] = Pass(acrepr, wirenum, int(m.group(2)))
            else:
                acrepr.wires[wirenum] = Const(wirenum, int(m.group(3)))
            continue

        #### input
        m = inPat.match(line)
        if m is not None:
            wirenum = get_wirenum(acrepr, m.group(1))
            innum = int(m.group(2))

            if rdlrepr is None:
                acrepr.wires[wirenum] = Input(acrepr, wirenum, innum)
                continue

            posn = acrepr.in_posn_curr
            acrepr.in_posn_curr += 1
            rdlOutNum = rdlrepr.out_posns[posn]
            rdlOut = rdlrepr.wires[rdlOutNum]

            # constant propagated from RDL
            if isinstance(rdlOut, Const):
                acrepr.wires[wirenum] = Const(wirenum, rdlOut.const)
                continue

            # otherwise, output gate in RDL
            assert isinstance(rdlOut, Output), "Expected Const or Output from RDL, got neither"
            assert len(rdlOut.uses) == 1, "Output gate in RDL had wrong number of uses"
            rdlInNum = rdlOut.uses[0]
            rdlIn = rdlrepr.wires[rdlInNum]
            wire = innum_to_wire.get(rdlIn.innum)
            if wire is not None:
                acrepr.wires[wirenum] = Pass(acrepr, wirenum, wire)
            else:
                innum_to_wire[rdlIn.innum] = wirenum
                acrepr.wires[wirenum] = Input(acrepr, wirenum, innum)

            continue

        #### output
        m = outPat.match(line)
        if m is not None:
            wirenum = get_wirenum(acrepr, m.group(1), True)
            wire = int(m.group(2))

            if wirenum in acrepr.wires and wire == wirenum:
                # Ox = Vy, x=y; this is valid PWS syntax

                # move existing wire to a safe holding spot
                wire = wirenum + WOFF5
                assert wire not in acrepr.wires, "error moving output wire: %d already exists" % wire
                oldGate = acrepr.wires[wirenum]
                oldGate.num = wire
                acrepr.wires[wire] = oldGate

                # edit the forward pointers to the moved gate
                for use in oldGate.uses:
                    useptrs = acrepr.whatuses[use]
                    useptrs.discard(wirenum)
                    useptrs.add(wire)

                # edit the back pointers to the moved gate
                successors = acrepr.whatuses.get(wirenum)
                if successors:      # need to point successors to the moved gate
                    del acrepr.whatuses[wirenum]
                    acrepr.whatuses[wire] = successors  # forward pointers from moved gate
                    for succNum in successors:          # back pointers to moved gate
                        succ = acrepr.wires[succNum]
                        succ.uses = [ wire if x == wirenum else x for x in succ.uses ]

            else:
                assert wirenum not in acrepr.wires, "multiply-driven wire %s" % wirenum

            acrepr.wires[wirenum] = Output(acrepr, wirenum, wire)
            if acrepr.out_posns is not None:
                acrepr.out_posns.append(wirenum)
            continue

        # otherwise it's something we don't recognize
        assert False, "unhandled line '%s' in input" % line

def optimize(acrepr, opt_constout):
    # step 2: dead and redundant gate elimination, const and pass propagation

    # 2a: constant propagation
    queue = deque(acrepr.gates(Const))
    while queue:
        gateNum = queue.popleft()
        gate = acrepr.wires[gateNum]
        # done with this constant, remove it
        del acrepr.wires[gateNum]

        # propagate constant to each successor
        successors = acrepr.whatuses.get(gateNum)
        if successors is None:
            continue
        del acrepr.whatuses[gateNum]
        for succNum in successors:
            append = False
            succ = acrepr.wires[succNum]
            uses = [ x for x in succ.uses if x != gateNum ]
            assert len(uses) < 2
            if isinstance(succ, Pass):
                assert not uses
                # pass gate just turns into a constant
                acrepr.wires[succNum] = Const(succNum, gate.const)
                append = True

            elif isinstance(succ, Mul):
                # multiplication gate turns into a constant, constmul, or pass
                if gate.const == 0:
                    acrepr.wires[succNum] = Const(succNum, 0)
                    append = True
                    if uses:
                        # gate formerly taking an input has become Const; remove forward connection
                        acrepr.whatuses[uses[0]].discard(succNum)
                elif gate.const == 1:
                    acrepr.wires[succNum] = Pass(acrepr, succNum, uses[0])
                elif uses:
                    acrepr.wires[succNum] = ConstMul(acrepr, succNum, uses[0], gate.const)
                else:
                    acrepr.wires[succNum] = Const(succNum, gate.const * gate.const)
                    append = True

            elif isinstance(succ, Add) and not succ.neg:
                # add gate turns into a constant, a constadd, or a pass
                if not uses:
                    # const + const
                    acrepr.wires[succNum] = Const(succNum, gate.const + gate.const)
                    append = True
                elif gate.const == 0:
                    # 0 + wire = pass(wire)
                    acrepr.wires[succNum] = Pass(acrepr, succNum, uses[0])
                else:
                    # const + wire
                    acrepr.wires[succNum] = ConstAdd(acrepr, succNum, uses[0], gate.const, False)

            elif isinstance(succ, Add):
                # subtract gate turns into a constant, a constadd, or a pass
                if not uses:
                    # const - const = 0
                    acrepr.wires[succNum] = Const(succNum, 0)
                    append = True
                elif succ.uses[0] == gateNum:
                    # const - wire
                    acrepr.wires[succNum] = ConstAdd(acrepr, succNum, uses[0], gate.const, True)
                elif gate.const == 0:
                    # wire - 0 = pass(wire)
                    acrepr.wires[succNum] = Pass(acrepr, succNum, uses[0])
                else:
                    # wire - const = wire + -const
                    acrepr.wires[succNum] = ConstAdd(acrepr, succNum, uses[0], -gate.const, False)

            elif isinstance(succ, ConstMul):
                assert not uses
                acrepr.wires[succNum] = Const(succNum, gate.const * succ.const)
                append = True

            elif isinstance(succ, ConstAdd):
                assert not uses
                if succ.neg:
                    newconst = succ.const - gate.const
                else:
                    newconst = gate.const + succ.const
                acrepr.wires[succNum] = Const(succNum, newconst)
                append = True

            elif isinstance(succ, Output):
                assert not uses
                acrepr.wires[succNum] = Const(succNum, gate.const)
                if opt_constout:
                    append = True

            else:
                assert False, "invalid successor %s for %s" % (repr(succ), repr(gate))

            if append and succNum not in queue:
                queue.append(succNum)
    if opt_constout:
        assert not acrepr.gates(Const), repr(acrepr)

    # 2b: pass-gate elimination
    queue = acrepr.gates(Pass)
    for gateNum in queue:
        gate = acrepr.wires[gateNum]
        predNum = gate.uses[0]
        # this gate will no longer exist, so it doesn't use its predecessor any more
        acrepr.whatuses[predNum].discard(gateNum)
        # for each of this gate's successors, make it a successor of the predecessor instead
        successors = acrepr.whatuses.get(gateNum)
        if successors:
            acrepr.whatuses[predNum].update(successors)
            # second, update backward pointers for each successor
            for succNum in successors:
                succ = acrepr.wires[succNum]
                succ.uses = [ predNum if x == gateNum else x for x in succ.uses ]
            del acrepr.whatuses[gateNum]
        # finally, delete the current gate
        del acrepr.wires[gateNum]
    assert not acrepr.gates(Pass), repr(acrepr)

    # 2c: dead gate elim: backward pass from outputs
    queue = deque(acrepr.gates((Output, Const)))
    while queue:
        gateNum = queue.popleft()
        if gateNum not in acrepr.wires:
            raise ValueError("Detected an undriven wire in your PWS. Please fix!")
        gate = acrepr.wires[gateNum]
        if gate.reached:
            continue
        gate.reached = True
        for v in gate.uses:
            queue.append(v)

    removes = set( w for w in acrepr.wires if not acrepr.wires[w].reached )
    for r in removes:
        for use in acrepr.wires[r].uses:
            if use not in removes:
                acrepr.whatuses[use].discard(r)
        del acrepr.wires[r]
    for r in removes:
        if r in acrepr.whatuses:
            del acrepr.whatuses[r]
    del removes

    # 2d: redundant gate elimination: forward pass, hash gates and replace redundant ones
    found = {}
    queue = deque(acrepr.gates(Input))
    while queue:
        gateNum = queue.popleft()
        if gateNum not in acrepr.wires:
            # reached an already-deleted gate
            continue
        gate = acrepr.wires[gateNum]
        gateHash = gate.hash_repr()

        # reached an output or re-visiting a gate we've already seen
        if isinstance(gate, Output) or not gate.reached:
            continue

        # for all other gates, mark reached, add successors to queue, check uniqueness
        gate.reached = False    # False because all gates surviving DGE have reached=True
        queue.extend(acrepr.whatuses[gateNum])
        if isinstance(gate, Input):
            # inputs are always unique
            continue
        elif gateHash not in found:
            # this gate is unique, so add to hash
            found[gateHash] = gateNum
            continue

        # found a non-unique gate. Remove it and reconnect its successors
        replNum = found[gateHash]

        # first, remove gate from predecessors' use-list
        for use in gate.uses:
            acrepr.whatuses[use].discard(gateNum)

        # second, update back-pointers from successors
        successors = acrepr.whatuses[gateNum]
        for succNum in successors:
            succ = acrepr.wires[succNum]
            succ.uses = [ x if x != gateNum else replNum for x in succ.uses ]

        # third, update forward pointer from replacement gate
        acrepr.whatuses[replNum].update(successors)

        # finally, delete this gate
        del acrepr.wires[gateNum]
        del acrepr.whatuses[gateNum]

def label_terminals(acrepr):
    count = 0
    for m in acrepr.gates(Mul):
        acrepr.wires[m].set_label(count)
        count += 1
    acrepr.num_muls = count
    acrepr.dummy_start = count

    count = -1
    for m in acrepr.gates(Input):
        acrepr.wires[m].set_label(count)
        count -= 1

def mul_constr_val(constr, val):
    ret = dict()
    for c in constr:
        ret[c] = val * constr[c]
    return ret

def add_constr_val(constr, val):
    ret = dict(constr)
    return add_constr_val_inplace(ret, val)

def add_constr_val_inplace(constr, val):
    constr['CONSTANT'] = constr.get('CONSTANT', 0) + val
    return constr

def add_constrs(constr1, constr2):
    ret = dict()
    for c in set(constr1.keys() + constr2.keys()):
        ret[c] = constr1.get(c, 0) + constr2.get(c, 0)
    return ret

def sub_constrs(constr1, constr2):
    ret = dict()
    for c in set(constr1.keys() + constr2.keys()):
        ret[c] = constr1.get(c, 0) - constr2.get(c, 0)
    return ret

def get_constrs(gate):
    if isinstance(gate, (Mul, Input)):
        return {gate.label: 1}
    return gate.constrs

def generate_constrs(acrepr, uses):
    count = 0
    heap = []
    for use in uses:
        heap.append((0, count, use))
        count += 1

    while heap:
        (prio, _, gateNum) = heapq.heappop(heap)
        gate = acrepr.wires[gateNum]
        if get_constrs(gate) is not None:
            # this takes care of Mul and Input gates, and any other gates we've already visited
            pass

        elif isinstance(gate, ConstMul):
            rGateNum = gate.uses[0]
            rGate = acrepr.wires[rGateNum]
            if get_constrs(rGate) is None:
                # prior gate needs to be visited first
                heapq.heappush(heap, (prio - 1, count, rGateNum))
                heapq.heappush(heap, (prio, count + 1, gateNum))
                count += 2
                continue

            # if we've gotten here, then the prior gate's constraints are ready to go
            gate.constrs = mul_constr_val(get_constrs(rGate), gate.const)

        elif isinstance(gate, ConstAdd):
            rGateNum = gate.uses[0]
            rGate = acrepr.wires[rGateNum]
            if get_constrs(rGate) is None:
                # prior gate needs to be visited first
                heapq.heappush(heap, (prio - 1, count, rGateNum))
                heapq.heappush(heap, (prio, count + 1, gateNum))
                count += 2
                continue

            # if we've gotten here, prior gate is ready to go
            if gate.neg:
                gate.constrs = add_constr_val_inplace(mul_constr_val(get_constrs(rGate), -1), gate.const)
            else:
                gate.constrs = add_constr_val(get_constrs(rGate), gate.const)

        elif isinstance(gate, Add):
            lGateNum = gate.uses[0]
            lGate = acrepr.wires[lGateNum]
            rGateNum = gate.uses[1]
            rGate = acrepr.wires[rGateNum]
            added = False
            if get_constrs(lGate) is None:
                # need to visit left gate
                heapq.heappush(heap, (prio - 1, count, lGateNum))
                count += 1
                added = True
            if get_constrs(rGate) is None:
                # need to visit right gate
                heapq.heappush(heap, (prio - 1, count, rGateNum))
                count += 1
                added = True
            if added:
                # if we need to visit either left or right, revisit this one, too
                heapq.heappush(heap, (prio, count, gateNum))
                count += 1
                continue

            # if we've gotten here, prior gates are ready to go
            if gate.neg:
                gate.constrs = sub_constrs(get_constrs(lGate), get_constrs(rGate))
            else:
                gate.constrs = add_constrs(get_constrs(lGate), get_constrs(rGate))

        else:
            assert False, "unexpected gate %s" % repr(gate)

def generate_all_constraints(acrepr):
    for term in acrepr.gates((Output, Mul)):
        generate_constrs(acrepr, acrepr.wires[term].uses)

def get_const_in_vals(acrepr, aconstr, bconstr, cconstr, mul_num, is_right):
    removes = []

    # first, handle constant value
    constval = {0: 0}
    if 'CONSTANT' in cconstr:
        cval = cconstr['CONSTANT']
        constval[0] = cval if mul_num is None else -cval
        removes.append('CONSTANT')

    # next, handle input values
    for idx in cconstr:
        if idx >= 0:
            continue

        using_mul_input = False
        removes.append(idx)                 # taking it out of cconstr when we're done
        mul = cconstr[idx]                  # get the coefficient value
        inlabel = acrepr.inputlabels[idx]   # and the corresponding input number
        if inlabel in acrepr.public_inputs:
            # this is a public input, so just push its value into the const
            constval[1+inlabel] = -mul
            continue

        elif inlabel in acrepr.priv_input_map:
            # we've run into this (private) inlabel before
            (is_b, priv_in) = acrepr.priv_input_map[inlabel]

        else:
            # don't need to allocate if this is a multiplier directly connected to an input
            # NOTE: (need to find these first or this optimization could get stepped on)
            if mul_num is not None and len(cconstr) == 1:
                is_b = is_right
                priv_in = acrepr.wires[mul_num].label
                using_mul_input = True

            ## we've never seen this (private) input before! allocate one
            # have we already half-allocated a dummy multiplier? then use it.
            elif acrepr.next_label is not None:
                is_b = True
                priv_in = acrepr.next_label
                acrepr.next_label = None

            # need to allocate a new dummy multiplier
            else:
                is_b = False
                priv_in = acrepr.num_muls
                acrepr.num_muls += 1
                acrepr.next_label = priv_in

            # save off this value in the private input map
            acrepr.priv_input_map[inlabel] = (is_b, priv_in)

        # put the coefficient on the correct pseudo-multiplier
        target_map = bconstr if is_b else aconstr
        if using_mul_input:
            assert target_map[priv_in] == -1, 'something fishy: expected mul value missing'
            del target_map[priv_in]     # it's an input, so it's unconstrained
        else:
            assert not priv_in in target_map, 'value already assigned to priv_in(%d) coeff' % priv_in
            target_map[priv_in] = mul

    for r in removes:
        del cconstr[r]

    if mul_num is None:
        # kludge: is_right is the output number
        constval[-(1+is_right)] = 1

    # when an input is directly connected to a multiplier input, it doesn't get a consistency constraint
    if not aconstr and not bconstr and not cconstr:
        return None
    return (aconstr, bconstr, cconstr, constval)

def collect_constraints(acrepr):
    # sort by shortest constraints first --- we need to do this to make sure we
    # don't allocate unnecessary dummy muls in below calls to get_consts_in_vals()
    def mulkey(m):
        uses = acrepr.wires[m].uses
        l0 = len(get_constrs(acrepr.wires[uses[0]]))
        l1 = len(get_constrs(acrepr.wires[uses[1]]))
        return min(l0, l1)

    for termNum in sorted(acrepr.gates(Mul), None, mulkey):
        term = acrepr.wires[termNum]

        cconstr1 = dict(get_constrs(acrepr.wires[term.uses[0]]))
        cconstr2 = dict(get_constrs(acrepr.wires[term.uses[1]]))
        acrepr.add_constr(get_const_in_vals(acrepr, {term.label: -1}, {}, cconstr1, termNum, False))
        acrepr.add_constr(get_const_in_vals(acrepr, {}, {term.label: -1}, cconstr2, termNum, True))

    for termNum in acrepr.gates(Output):
        term = acrepr.wires[termNum]

        cconstr = dict(get_constrs(acrepr.wires[term.uses[0]]))
        acrepr.add_constr(get_const_in_vals(acrepr, {}, {}, cconstr, None, term.num))

def pws_to_constraints(fh, public_inputs, rdlfh):
    if rdlfh is not None:
        rdlrepr = ACRepr(True)
        parse(rdlrepr, rdlfh, None)     # need the RDL to parse the AC
        optimize(rdlrepr, False)

        acrepr = ACRepr()
        parse(acrepr, fh, rdlrepr)

        del rdlrepr
    else:
        acrepr = ACRepr()
        parse(acrepr, fh, None)
    acrepr.public_inputs = public_inputs

    optimize(acrepr, True)
    label_terminals(acrepr)
    generate_all_constraints(acrepr)
    collect_constraints(acrepr)

    return acrepr

def main():
    if len(sys.argv) < 2:
        sys.exit("usage: " + sys.argv[0] + " <infile.pws> [<priv_input_numbers>]")
    elif len(sys.argv) < 3 or not sys.argv[2]:
        pubins = [0]
    else:
        pubins = [ int(x) for x in sys.argv[2].split(',') ]

    infile = sys.argv[1]
    if len(sys.argv) > 3:
        rdlfile = sys.argv[3]
    else:
        rdlfile = None

    with open(infile, 'r') as fh:
        if rdlfile is not None:
            with open(rdlfile, 'r') as rfh:
                print repr(pws_to_constraints(fh, pubins, rfh))
        else:
            print repr(pws_to_constraints(fh, pubins, None))

if __name__ == "__main__":
    main()
