import FraudProof.Value
import FraudProof.MTree
import FraudProof.Hash

import Mathlib.Data.Sum.Basic

def hashElem : BTree Value ⊕ BTree Value  → PathElem :=
  let hashTree := ( MTree.hash ∘ hash_BTree )
  Sum.map  hashTree hashTree

----------------------------------------
-- Tree Path to Hash Path
@[simp]
def treeTohashPath : TreePath Value  → Path :=
  List.map hashElem

@[simp]
lemma TreeLenEq
  : (treeTohashPath path).length = path.length
  := by exact List.length_map _ _

lemma RevTreeLenEq ( path : TreePath Value )
  : (treeTohashPath path).reverse.length = path.length
  := by simp

----------------------------------------


def sumP {α : Type}  : Sum α α → α := (Sum.elim id id)

-- PathComputation v p = List.drop 1 (ScanPath v p)
@[simp]
def ScanPath ( v : Hash ) ( path : Path ) : List Hash
:= List.scanl opHash v path
