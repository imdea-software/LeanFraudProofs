import FraudProof.Value
import FraudProof.BTree
import FraudProof.Hash

-- Pure definition of Merkle Tree
inductive MTree : Type
  | node (h : Hash)

def MTree.hash : MTree → Hash
  | node h => h

def comb_MTree ( tL tR : MTree ) : MTree :=
    match tL , tR with
    | MTree.node hL , MTree.node hR => MTree.node (hL ⊕ hR)

def hash_BTree (t : BTree Value) : MTree :=
match t with
| BTree.leaf v => MTree.node (H v)
| BTree.node hL hR => comb_MTree ( hash_BTree hL ) ( hash_BTree hR )

----------------------------------------
-- * Paths
-- Path in Merkle Trees are hashes indicating its position.
abbrev PathElem := Sum Hash Hash

abbrev Path := List PathElem

def opHash (h : Hash) (e : PathElem) : Hash :=
match e with
| Sum.inl hl => hl ⊕ h
| Sum.inr hr => h ⊕ hr

-- Get the result of applying a path to a hash
-- Notice that the length of the path is very important
@[simp]
def listPathHashes (h : Hash) (path : Path) : Hash :=
 List.foldl opHash h path
-- match path wit
--     | [] => h
--     | (p :: ps) => listPathHashes (opHash h p) ps
----------------------------------------
-- Merkle Tree operations

-- Hash |h| (representing a node) is in tree |t| if path |path| leads to it.
def nodeIn (h : Hash) (path : Path) (t : MTree) : Bool
:= match t with
| MTree.node hT => listPathHashes h path == hT

-- Same but at value level.
def containCompute (v : Value) (path : Path) (t : MTree) : Bool
:= nodeIn (H v) path t
--

----------------------------------------
-- * Element contantion
theorem leftChildContaintionN (v : Value) (btR broot : BTree Value) :
    -- Node (Leaf v) tree
    broot = BTree.node (BTree.leaf v) btR ->
    -- tree has a hash (not empty)
    MTree.node h = hash_BTree btR ->
    -- then we can prove the element is in the merkle tree.
    containCompute v ([ Sum.inr h  ]) (hash_BTree broot)
:= by
   intros HRoot BtHash
   rw [containCompute]
   rw [nodeIn, HRoot]
   rw [ hash_BTree , hash_BTree, comb_MTree]
   rw [ <- BtHash ]
   simp
   unfold opHash
   simp

theorem rightChildContaintionN (v : Value) (btL broot : BTree Value) :
    -- Node (Leaf v) tree
    broot = BTree.node btL (BTree.leaf v) ->
    -- tree has a hash (not empty)
    MTree.node h = hash_BTree btL ->
    -- then we can prove the element is in the merkle tree.
    containCompute v ([ Sum.inl h  ]) (hash_BTree broot)
:= by { -- same as before
        intros HRoot BtHash
        rw [containCompute , nodeIn, HRoot]
        rw [ hash_BTree , hash_BTree, comb_MTree]
        rw [ <- BtHash ]
        simp
        unfold opHash
        simp
    }

theorem leafChildContaintionN (v : Value) (broot : BTree Value) :
    -- Node (Leaf v) tree
    broot = BTree.leaf v ->
    containCompute v [] (hash_BTree broot)
:= by {
    intros HRoot
    rw [ containCompute, nodeIn, HRoot, hash_BTree ]
    simp
}
