import FraudProof.DataStructures.Value
import FraudProof.DataStructures.BTree
import FraudProof.DataStructures.Hash

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

abbrev SkElem := Sum Unit Unit

@[simp]
def SkElem.fill (skl : SkElem) (h : Hash) : PathElem
  := match skl with
    | Sum.inl _ => Sum.inl h
    | Sum.inr _ => Sum.inr h

@[simp]
def PathElem.forget (h : PathElem) : SkElem
  := match h with
     | Sum.inl _ => Sum.inl ()
     | Sum.inr _ => Sum.inr ()

abbrev Path := List PathElem
abbrev Skeleton := List SkElem

@[simp]
def Skeleton.fill (skl : Skeleton) (hs : Fin skl.length -> Hash) : Path
 := match skl with
    | List.nil => List.nil
    | List.cons s ss => s.fill (hs ⟨ 0 , by simp ⟩ )  :: Skeleton.fill ss (fun p => hs ⟨ p.val + 1 , by simp ⟩)

@[simp]
def MapSeq {α β : Type} { n : Nat } (f : α → β)
  : (Fin n -> α) -> (Fin n -> β) := fun s p => f $ s p

@[simp]
def MapSeqKey {α β : Type} {n : Nat} (f : Nat -> α -> β)
  : (Fin n -> α) -> (Fin n -> β) := fun s p => f p.val $ s p

@[simp]
def SeqForget { n : Nat } : (Fin n -> PathElem) -> (Fin n -> SkElem)
  := MapSeq PathElem.forget

def opHash (h : Hash) (e : PathElem) : Hash :=
match e with
| Sum.inl hl => hl ⊕ h
| Sum.inr hr => h ⊕ hr

theorem opHash_neqRight {hl hr : Hash} {pl pr : Hash}
 : ¬ (hl = hr) -> ¬ opHash hl (Sum.inl pl) = opHash hr (Sum.inl pr)
 := by intro H
       simp [ opHash ]
       apply hop_neq_right
       assumption

theorem opHash_neqLeft {hl hr : Hash} {pl pr : Hash}
 : ¬ (hl = hr) -> ¬ opHash hl (Sum.inr pl) = opHash hr (Sum.inr pr)
 := by intro H
       simp [ opHash ]
       apply hop_neq_left
       assumption

theorem opHash_neq {hl hr : Hash} {path : PathElem}-- {el er : PathElem}
  : ¬ (hl = hr) -> ¬ opHash hl path = opHash hr path
  := by
  intro hneq
  unfold opHash
  cases path with
  | inl pl => simp; apply hop_neq_right; assumption
  | inr pl => simp; apply hop_neq_left ; assumption

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
theorem leftChildContaintionN (v : Value) (h : Hash) (btR broot : BTree Value) :
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

theorem rightChildContaintionN (v : Value) (h : Hash) (btL broot : BTree Value) :
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
