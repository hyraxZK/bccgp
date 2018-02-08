#!/usr/bin/python
#
# (C) 2018 Riad S. Wahby <rsw@cs.stanford.edu>

import sys

import libbccgp.bccgp as bccgp
import libbccgp.bullet as bullet
import libbccgp.pws as pws
import libbccgp.solve as solve

if sys.version_info[0] != 2 or sys.version_info[1] < 7:
    sys.exit("ERROR: this software Python 2.7!")
