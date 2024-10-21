-- import FraudProof.DataStructures.Value
import FraudProof.DataStructures.BTree
import FraudProof.DataStructures.Hash

inductive MTree (ℍ : Type): Type
  | node (h : ℍ)

-- notation
def MTree.hash {ℍ : Type} : MTree ℍ → ℍ
  | node h => h

def comb_MTree {ℍ : Type}[m : HashMagma ℍ] (tL tR : MTree ℍ) : MTree ℍ:=
 match tL , tR with
 | MTree.node hL , MTree.node hR => MTree.node (m.comb hL hR)

def hash_BTree { α ℍ : Type}[o : Hash α ℍ][HashMagma ℍ] (t : BTree α) : MTree ℍ:=
  match t with
  | BTree.leaf v => MTree.node (o.mhash v)
  | BTree.node hL hR => comb_MTree ( hash_BTree hL ) ( hash_BTree  hR )

----------------------------------------
-- * Paths
-- Path in Merkle Trees are hashes indicating its position.
abbrev PathElem (ℍ : Type) := Sum ℍ ℍ
abbrev SkElem := Sum Unit Unit

@[simp]
def SkElem.fill {ℍ : Type}(skl : SkElem) (h : ℍ) : PathElem ℍ
  := match skl with
    | Sum.inl _ => Sum.inl h
    | Sum.inr _ => Sum.inr h

@[simp]
def PathElem.forget {ℍ : Type}(h : PathElem ℍ) : SkElem
:= match h with
    | Sum.inl _ => Sum.inl ()
    | Sum.inr _ => Sum.inr ()

abbrev Path (ℍ : Type):= List (PathElem ℍ)
abbrev Skeleton := List SkElem

@[simp]
def Skeleton.fill {ℍ : Type}(skl : Skeleton) (hs : Fin skl.length -> ℍ) : Path ℍ
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
def SeqForget {ℍ : Type} { n : Nat } : (Fin n -> PathElem ℍ) -> (Fin n -> SkElem)
:= MapSeq PathElem.forget

def opHash {ℍ : Type}[m : HashMagma ℍ] (h : ℍ) (e : PathElem ℍ) : ℍ :=
match e with
| Sum.inl hl => m.comb hl h
| Sum.inr hr => m.comb h hr

theorem opHash_neqRight {ℍ : Type}[ HashMagma ℍ][lHStr : SLawFulHash ℍ] {hl hr : ℍ} {pl pr : ℍ}
: ¬ (hl = hr) -> ¬ opHash hl (Sum.inl pl) = opHash hr (Sum.inl pr)
:= by intro H
      simp [ opHash ]
      apply lHStr.neqRight -- hop_neq_right
      assumption

theorem opHash_neqLeft {ℍ : Type}[ HashMagma ℍ][lHStr : SLawFulHash ℍ]{hl hr : ℍ} {pl pr : ℍ}
: ¬ (hl = hr) -> ¬ opHash hl (Sum.inr pl) = opHash hr (Sum.inr pr)
:= by intro H
      simp [ opHash ]
      apply lHStr.neqLeft
      assumption

theorem opHash_neq {ℍ : Type}[ HashMagma ℍ][lHStr : SLawFulHash ℍ] {hl hr : ℍ} {path : PathElem ℍ}-- {el er : PathElem}
: ¬ (hl = hr) -> ¬ opHash hl path = opHash hr path
:= by
intro hneq
unfold opHash
cases path with
| inl pl => simp; apply lHStr.neqRight; assumption
| inr pl => simp; apply lHStr.neqLeft ; assumption

-- Get the result of applying a path to a hash
-- Notice that the length of the path is very important
@[simp]
def listPathHashes {ℍ : Type}[HashMagma ℍ](h : ℍ) (path : Path ℍ) : ℍ :=
List.foldl opHash h path

----------------------------------------
-- Merkle Tree operations

-- Hash |h| (representing a node) is in tree |t| if path |path| leads to it.
def nodeIn {ℍ : Type}[ BEq ℍ ][HashMagma ℍ](h : ℍ )(path : Path ℍ) (t : MTree ℍ) : Bool
:= match t with
| MTree.node hT => listPathHashes h path == hT

-- Same but at value level.
def containCompute {α ℍ : Type}[ BEq ℍ ][o : Hash α ℍ][HashMagma ℍ](v : α) (path : Path ℍ) (t : MTree ℍ) : Bool
:= nodeIn (o.mhash v) path t

----------------------------------------
-- * Element contantion
theorem leftChildContaintionN {α ℍ : Type}[BEq ℍ][LawfulBEq ℍ][Hash α ℍ][HashMagma ℍ](v : α) (h : ℍ) (btR broot : BTree α) :
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


theorem rightChildContaintionN {α ℍ : Type}[BEq ℍ][LawfulBEq ℍ][Hash α ℍ][HashMagma ℍ](v : α) (h : ℍ) (btL broot : BTree α) :
    -- Node (Leaf v) tree
    broot = BTree.node btL (BTree.leaf v) ->
    -- tree has a hash (not empty)
    MTree.node h = hash_BTree btL ->
    -- then we can prove the element is in the merkle tree.
    containCompute v ([ Sum.inl h  ]) (hash_BTree broot)
:= by
        intros HRoot BtHash
        rw [containCompute , nodeIn, HRoot]
        rw [ hash_BTree , hash_BTree, comb_MTree]
        rw [ <- BtHash ]
        simp
        unfold opHash
        simp

theorem leafChildContaintionN {α ℍ : Type}[BEq ℍ][LawfulBEq ℍ][Hash α ℍ][HashMagma ℍ](v : α) (broot : BTree α) :
    -- Node (Leaf v) tree
    broot = BTree.leaf v ->
    -- We need to be explicit because of the polimophisim of |[] :: List ℍ|
    @containCompute α ℍ _ _ _ v [] (hash_BTree broot)
:= by intros HRoot; rw [ containCompute, nodeIn, HRoot, hash_BTree ]; simp
