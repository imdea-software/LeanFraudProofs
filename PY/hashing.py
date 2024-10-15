#!/home/mceresa/Research/WIP/LeanPOC/FraudProof/PY/venv/bin/python

from web3 import Web3 # hashfunctions.
from hexbytes import HexBytes # prettier representation

import sys # basic argument

# args
if len(sys.argv) >= 2:
    arg = sys.argv[1]
    # karg = Web3.solidity_keccak(['string'],[arg])
    karg = Web3.keccak(text=arg)
    hexBarg = HexBytes(karg)
    print(hexBarg.hex())
else:
    print("Bad Args")
    exit(-1)
