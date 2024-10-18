import FraudProof.DataStructures.Hash

import Batteries.Lean.IO.Process -- easy run process

------------------------------------------------------------
-- Absolute path to python hash function.
def python : String
  := "/home/mceresa/Research/WIP/LeanPOC/FraudProof/PY/venv/bin/python"
def pyHash : String
  := "/home/mceresa/Research/WIP/LeanPOC/FraudProof/PY/hashing.py"

------------------------------------------------------------
-- Running pyHash script
def externalHashing' (str : String) : IO (Option String) :=
  IO.Process.runCmdWithInput' python (Array.mkArray2 pyHash str) >>=
  fun res => return if res.stderr != "" then  none else some res.stdout

def externalHashing (str : String) : IO String :=
  IO.Process.runCmdWithInput python (Array.mkArray2 pyHash str)

def combHashing (str1 str2 : String) : IO String :=
  -- str1 ⊕ str2 = H(str1 ++ str2)
  externalHashing (str1.append str2)


------------------------------------------------------------

------------------------------------------------------------
-- Main entry point.
def main : IO Unit :=
  do
    let enc <- externalHashing "hasheame"
    IO.println "Hello! This is goint to be a simple demo of our humble piece of software"
    IO.println s!"Hashed:{enc}"

------------------------------------------------------------
