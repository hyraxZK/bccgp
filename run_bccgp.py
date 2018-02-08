#!/usr/bin/python
#
# (C) Riad S. Wahby <rsw@cs.stanford.edu>
#
# run BCCGP and/or Bulletproofs

import getopt
import os.path as OP
import subprocess
import resource
import sys
import time
import traceback

from libbccgp import bccgp, bullet, pws

from libfennel.defs import Defs
from libfennel.fiatshamir import FiatShamir
import libfennel.util as util

class VerifierInfo(object):
    nCopies = 1
    pwsFile = None
    rdlFile = None
    public_inputs = []
    curve = 'm191'

    logFile = None

    showPerf = False
    pStartTime = 0
    pEndTime = 0
    vStartTime = 0
    vEndTime = 0

    bullet = False

    class Log(object):
        logLines = []

        @classmethod
        def get_lines(cls):
            for line in cls.logLines:
                yield line
                yield '\n'

        @classmethod
        def log(cls, lStr, do_print):
            cls.logLines.append(lStr)
            if do_print:
                print lStr

def get_pws():
    if VerifierInfo.nCopies == 1:
        return open(VerifierInfo.pwsFile, 'r')

    exe = OP.join(OP.dirname(OP.realpath(__file__)), 'pwsrepeat')
    nc = str(VerifierInfo.nCopies)
    p = subprocess.Popen([exe, VerifierInfo.pwsFile, nc], stdout=subprocess.PIPE)
    return p.stdout

def get_acrepr():
    with get_pws() as pFile:
        if VerifierInfo.rdlFile is not None:
            with open(VerifierInfo.rdlFile, 'r') as rFile:
                return pws.pws_to_constraints(pFile, VerifierInfo.public_inputs, rFile)

        return pws.pws_to_constraints(pFile, VerifierInfo.public_inputs, None)

def run_bccgp():
    # set prime
    Defs.curve = VerifierInfo.curve
    util.set_prime(bccgp.MiraclEC.get_order(Defs.curve))

    # compile the PWS into an acrepr and solve it
    acrepr = get_acrepr()

    # build and run the prover
    if VerifierInfo.bullet:
        prv = bullet.BulletProverNI(acrepr, VerifierInfo.curve)
    else:
        prv = bccgp.BCCGPSqrtProverNI(acrepr, VerifierInfo.curve)
    VerifierInfo.pStartTime = time.time()
    proof = prv.run({})
    VerifierInfo.pEndTime = time.time()
    VerifierInfo.Log.log("Proof size: %d elems, %d bytes" % FiatShamir.proof_size(proof), True)

    # build and run the verifier
    if VerifierInfo.bullet:
        ver = bullet.BulletVerifierNI(acrepr, VerifierInfo.curve)
    else:
        ver = bccgp.BCCGPSqrtVerifierNI(acrepr, VerifierInfo.curve)
    VerifierInfo.vStartTime = time.time()
    try:
        ver.run(proof)
    except Exception as e: # pylint: disable=broad-except
        VerifierInfo.Log.log("Verification failed: %s" % e, True)
        VerifierInfo.Log.log(traceback.format_exc(), True)
    else:
        VerifierInfo.Log.log("Verification succeeded.", True)
    VerifierInfo.vEndTime = time.time()

def get_usage():
    uStr =  "Usage: %s -p <pwsFile> [options]\n\n" % sys.argv[0]
    uStr += " option        description                                 default\n"
    uStr += " --            --                                          --\n"

    uStr += " -p pwsFile    PWS describing the computation to run.      (None)\n\n"

    uStr += " -r rdlFile    use RDL from file                           (None)\n\n"

    uStr += " -c nC         Set repeated #copies = 2^nC                 (%d)\n" % VerifierInfo.nCopies
    uStr += "               \"-c =<nCopies>\" means #copies instead of log2\n\n"

    uStr += " -n a,b,c,...  PWS identifiers for the public inputs.      ([])\n"
    uStr += "               All other inputs are assumed to be private.\n\n"

    uStr += " -b            Run Bulletproof instead of BCCGP            (False)\n\n"

    uStr += " -C <curve>    use curve <curve> (m159, m191, m221, m255)  (%s)\n\n" % VerifierInfo.curve

    uStr += " -T            show performance info when done             (False)\n\n"

    uStr += " -L <logfile>  log perf info to logfile                    (None)\n"

    return uStr

def main():
    uStr = get_usage()
    oStr = "c:p:r:n:C:L:Tb"

    try:
        (opts, args) = getopt.getopt(sys.argv[1:], oStr)
    except getopt.GetoptError as err:
        print uStr
        print str(err)
        sys.exit(1)

    if args:
        print uStr
        print "ERROR: extraneous arguments."
        sys.exit(1)

    for (opt, arg) in opts:
        if opt == "-c":
            if arg[0] == "=":
                nC = int(arg[1:])
            else:
                nCB = int(arg)
                nC = 1 << nCB
            VerifierInfo.nCopies = nC
        elif opt == "-p":
            VerifierInfo.pwsFile = arg
        elif opt == "-r":
            VerifierInfo.rdlFile = arg
        elif opt == "-n":
            VerifierInfo.public_inputs = [ int(x) for x in arg.split(',') ]
        elif opt == "-C":
            VerifierInfo.curve = arg
        elif opt == "-T":
            VerifierInfo.showPerf = True
        elif opt == "-L":
            VerifierInfo.logFile = arg
        elif opt == "-b":
            VerifierInfo.bullet = True
        else:
            assert False, "logic error: got unexpected option %s from getopt" % opt

    if VerifierInfo.pwsFile is None:
        print uStr
        print "ERROR: missing required argument, -p <pwsFile>."
        sys.exit(1)

    run_bccgp()

    VerifierInfo.Log.log("Prover runtime: %f" % (VerifierInfo.pEndTime - VerifierInfo.pStartTime), VerifierInfo.showPerf)
    VerifierInfo.Log.log("Verifier runtime: %f" % (VerifierInfo.vEndTime - VerifierInfo.vStartTime), VerifierInfo.showPerf)
    VerifierInfo.Log.log("Max memory usage: %d kB" % resource.getrusage(resource.RUSAGE_SELF).ru_maxrss, VerifierInfo.showPerf)

    if VerifierInfo.logFile is not None:
        with open(VerifierInfo.logFile, 'w') as fh:
            fh.writelines(VerifierInfo.Log.get_lines())

if __name__ == "__main__":
    main()
