import FraudProof.DataStructures.Hash
import FraudProof.DataStructures.BTree
import FraudProof.DataStructures.MTree

import Batteries.Lean.IO.Process -- easy run process

import Mathlib.Control.Combinators -- mapM and stuff

------------------------------------------------------------
-- Relative path to python hash function.
-- def python : String
--   := "/home/mceresa/Research/WIP/LeanPOC/FraudProof/PY/venv/bin/python"

section PythonRelPath
  open System
  variable (projectRoot : System.FilePath)
  def relPydir : System.FilePath
    := projectRoot.join $ mkFilePath ["PY"]

  def relPython : System.FilePath
    := (relPydir projectRoot).join $ mkFilePath ["venv","bin","python"]

  def relPyHash : System.FilePath
    := (relPydir projectRoot).join $ mkFilePath ["hashing.py"]
end PythonRelPath

-- File path definition plus some basic checks
def fileExistsOrError (fp : System.FilePath) : IO System.FilePath :=
  Monad.cond fp.pathExists (return fp) ( throw $ IO.userError s!"File {fp.toString} not found :-(" )


def pythonFileP : IO System.FilePath := relPython <$> IO.currentDir

def hashFileP : IO System.FilePath := relPyHash <$> IO.currentDir

------------------------------------------------------------
-- Running pyHash script
def externalHashing' (str : String) : IO (Option String) :=
  do
   let python <- pythonFileP
   let pyHash <- hashFileP
   let res <- IO.Process.runCmdWithInput' python.toString (Array.mkArray2 pyHash.toString str)
   if res.stderr != ""
     then return none
     else return (some res.stdout)

section PyHash
  variable (python pyhash : String)

    def externalHashing (str : String) : IO String :=
    IO.Process.runCmdWithInput python (Array.mkArray2 pyhash str)

    def combHashing (str1 str2 : String) : IO String :=
    externalHashing python pyhash (str1.append str2)

-- Hash instances (flagged as unsafe)
    unsafe instance ecck : Hash String String where
    mhash str := match unsafeIO $ externalHashing python pyhash str with
                | .error _ => ""
                | .ok h => h

    unsafe def unsafeExtComb (str1 str2 : String) : String
      := match unsafeIO (combHashing python pyhash str1 str2) with
        | .error _ => ""
        | .ok hash => hash

    unsafe instance ecckMagma : HashMagma String where
      comb := unsafeExtComb python pyhash
------------------------------------------------------------
-- * Laws
-- We only need laws to prove theorems.
--
-- All laws are assumed. Outside this work.
-- unsafe instance collfree : CollResistant String String where
--   noCollisions := sorry
-- unsafe instance magmaLaw : SLawFulHash String where
--   neqLeft := sorry
--   neqRight := sorry
------------------------------------------------------------

------------------------------------------------------------
-- * Small Demo with elements
-- .
-- Some elements, we can IO them.

-- unsafe def elemsHashes : List String := elements.map (ecck.mhash python pyhash)
-- unsafe def elemsTree : BTree String :=
--   match elemsHashes.fromList with
--     | none => sorry -- it's unsafe, I don't case about stuff anymore.
--     | some t => t

-- -- Get Merkle Tree
-- unsafe def elemsMTree : MTree String := hash_BTree elemsTree
------------------------------------------------------------
end PyHash
--------------------


def elements : List String := ["esto", "es", "una", "demo"]
------------------------------------------------------------
-- Main entry point.
def main : IO Unit :=
  do
    IO.println "Hello Human?"
    IO.println "This s a simple demo of our humble piece of software"
    -- Getting Hash function
    let python <- pythonFileP >>= fileExistsOrError
    let pyHash <- hashFileP >>= fileExistsOrError
    let hash := externalHashing python.toString pyHash.toString
    let magmaHash := combHashing python.toString pyHash.toString
    --
    IO.println s!"Elements of the tree :{elements}"
    let encs <- Monad.mapM hash elements
    IO.println s!"Hashed elements:{encs}"
    let btree := encs.fromList
    IO.println "Generated a balanced tree."
    match btree with
      | none => IO.println "empty tree?"
      | some t => do
                    let mt <- hashM hash magmaHash t
                    IO.println s!"And presents the following MTree root hash {mt.hash}"
------------------------------------------------------------
