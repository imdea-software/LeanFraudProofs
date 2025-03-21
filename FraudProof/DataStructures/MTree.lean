import FraudProof.DataStructures.BTree
import FraudProof.DataStructures.Hash
import FraudProof.DataStructures.Sequence

----------------------------------------
-- Merkle Tree are hashes plus an implicit invariant.
----------------------------------------
--

abbrev MTree (ℍ : Type) := ℍ

@[simp]
def comb_MTree {ℍ : Type}[m : HashMagma ℍ]
  : MTree ℍ -> MTree ℍ -> MTree ℍ := m.comb

@[simp]
def BTree.hash_BTree { α ℍ : Type}
  [o : Hash α ℍ][HashMagma ℍ] : BTree α -> MTree ℍ
  := fun t => t.fold o.mhash comb_MTree
-- @[simp]
def ABTree.hash_Tree {α ℍ : Type}
  [o : Hash α ℍ][m : HashMagma ℍ] : BTree α -> ABTree α ℍ
  := ABTree.fold .leaf (fun _ sl sr => .node ( m.comb (sl.getI' o.mhash id) (sr.getI' o.mhash id)) sl sr)

-- @[simp]
def ABTree.hash_SubTree {α ℍ : Type}
  [o : Hash α ℍ][m : HashMagma ℍ] : BTree α -> ABTree α (ℍ × ℍ)
  := ABTree.fold .leaf ( fun _ sl sr =>
                               .node ( sl.getI' o.mhash (fun (l,r) => m.comb l r)
                                     , sr.getI' o.mhash (fun (l,r) => m.comb l r) )
                                     sl sr )

structure MkData (ℍ : Type) where
 top : ℍ
 left : ℍ
 right : ℍ

def ABTree.merkle_root {α ℍ : Type}
   [o : Hash α ℍ] : ABTree α (MkData ℍ) -> ℍ
   := ABTree.getI' o.mhash (·.top)

def ABTree.hash_MKSubts {α ℍ : Type}
  [Hash α ℍ][m : HashMagma ℍ] : BTree α -> ABTree α (MkData ℍ)
  := ABTree.fold .leaf (fun _ bl br =>
       have bl_mkroot := bl.merkle_root
       have br_mkroot := br.merkle_root
       node
       { top :=  m.comb bl_mkroot br_mkroot
       , left := bl_mkroot
       , right := br_mkroot}
       bl br)

-- Eff HashingTree
def hashM {α ℍ : Type}{m : Type -> Type}[Monad m]
    (hL : α -> m ℍ)(hC : ℍ -> ℍ -> m ℍ)(t : BTree α) : m (MTree ℍ)
    := match t with
      | .leaf v => hL v
      | .node nL nR =>
        do let l <- hashM hL hC nL
           let r <- hashM hL hC nR
           hC l r

----------------------------------------
-- * Paths
-- Path in Merkle Trees are hashes indicating its position.
--
inductive SkElem : Type where | Left | Right

instance : BEq SkElem where
  beq l r :=
    match l, r with
    | .Left, .Left => true
    | .Right, .Right => true
    | _ , _ => false

instance : LawfulBEq SkElem where
  eq_of_beq := by
    intros a b
    cases a
    all_goals { cases b ; all_goals {simp}}
  rfl := by intro a; cases a <;> decide

def SkElem.destruct {α : Type}(s : SkElem) (l r : α) : α
  := match s with | .Left => l | .Right => r

-- Unbound paths
abbrev Skeleton := List SkElem
-- Bound paths
abbrev ISkeleton (n : Nat) := Sequence n SkElem
--

def ABTree.find_left {α β : Type}(is : α -> Bool) : ABTree α  β -> Option (List (SkElem × (α ⊕ β)))
 | .leaf v => if is v then .some .nil else .none
 | .node _b bl br =>
    match bl.find_left is with
    | .none => (br.find_left is).map (fun ls => ls.append [(.Right, bl.getI' .inl .inr)])
    | .some ls => .some $ ls.append [(.Left , br.getI' .inl .inr)]

-- a -> spine, sib
def ABTree.gen_path_elem_forward {α β γ : Type}{n : Nat}
 (t : ABTree α β) (ag : α -> γ)(bg : β -> γ) (p : Sequence n SkElem) : Option (α × Sequence n (γ × γ))
 := match n, t with
   | .zero , .leaf v => .some (v , .nil)
   | .succ _ , .node b bl br =>
      p.head.destruct
        ((bl.gen_path_elem_forward ag bg p.tail).map (fun (e, ls) => (e , ls.snoc (bg b, br.getI' ag bg))))
        ((br.gen_path_elem_forward ag bg p.tail).map (fun (e, ls) => (e , ls.snoc (bg b, bl.getI' ag bg))))
   | _ , _ => .none

----------------------------------------
-- @[simp]
-- def SeqForget {ℍ : Type} { n : Nat } : (Sequence n (PathElem ℍ)) -> (Sequence n SkElem)
-- := Sequence.map PathElem.forget

-- def opHash {ℍ : Type}[m : HashMagma ℍ] (h : ℍ) (e : PathElem ℍ) : ℍ :=
-- match e with
-- | Sum.inl hl => m.comb hl h
-- | Sum.inr hr => m.comb h hr

@[simp]
def op_side {ℍ : Type}[mag : HashMagma ℍ](side : SkElem) (a b : ℍ) : ℍ
  := match side with
    | .Left => mag.comb a b
    | .Right => mag.comb b a


theorem opHash_neqRight {ℍ : Type}[ HashMagma ℍ][lHStr : SLawFulHash ℍ] {hl hr : ℍ} {pl pr : ℍ}
: ¬ (hl = hr) -> ¬ op_side .Right hl pl = op_side .Right hr pr
:= by intro H
      simp
      apply lHStr.neqRight
      assumption

theorem opHash_neqLeft {ℍ : Type}[ HashMagma ℍ][lHStr : SLawFulHash ℍ]{hl hr : ℍ} {pl pr : ℍ}
: ¬ (hl = hr) -> ¬ op_side .Left hl pl = op_side .Left hr pr
:= by intro H
      simp
      apply lHStr.neqLeft
      assumption

@[simp]
def listPathHashes {ℍ : Type}[HashMagma ℍ](h : ℍ) (path : List (SkElem × ℍ)) : ℍ
  := List.foldl (fun h (s , l) => op_side s h l) h path

----------------------------------------
-- Merkle Tree operations

-- Hash |h| (representing a node) is in tree |t| if path |path| leads to it.
def nodeIn {ℍ : Type}[ BEq ℍ ][HashMagma ℍ](h : ℍ )(path : List (SkElem × ℍ)) (t : MTree ℍ) : Bool
  := listPathHashes h path == t

-- Same but at value level.
def containCompute {α ℍ : Type}[ BEq ℍ ][o : Hash α ℍ][HashMagma ℍ](v : α) (path : List (SkElem × ℍ)) (t : MTree ℍ) : Bool
  := nodeIn (o.mhash v) path t

----------------------------------------
-- * Element contantion
theorem leftChildContaintionN {α ℍ : Type}[BEq ℍ][LawfulBEq ℍ][Hash α ℍ][HashMagma ℍ](v : α) (h : ℍ) (btR broot : BTree α) :
    -- Node (Leaf v) tree
    broot = BTree.node (BTree.leaf v) btR ->
    -- tree has a hash (not empty)
    h = btR.hash_BTree ->
    -- then we can prove the element is in the merkle tree.
    containCompute v [ (.Left , h) ] broot.hash_BTree
:= by
    intros HRoot BtHash
    rw [containCompute]
    rw [nodeIn, HRoot]
    -- simp [BTree.hash_BTree, ABTree.fold] at BtHash
    simp
    rw [ BtHash ]
    simp [ BTree.hash_BTree, ABTree.fold ]

theorem rightChildContaintionN {α ℍ : Type}[BEq ℍ][LawfulBEq ℍ][Hash α ℍ][HashMagma ℍ](v : α) (h : ℍ) (btL broot : BTree α) :
    -- Node (Leaf v) tree
    broot = BTree.node btL (BTree.leaf v) ->
    -- tree has a hash (not empty)
    h = btL.hash_BTree ->
    -- then we can prove the element is in the merkle tree.
    containCompute v [ (.Right , h)  ] broot.hash_BTree
:= by intros HRoot BtHash
      rw [containCompute , nodeIn, HRoot, BtHash]
      simp

theorem leafChildContaintionN {α ℍ : Type}[BEq ℍ][LawfulBEq ℍ][Hash α ℍ][HashMagma ℍ](v : α) (broot : BTree α) :
    -- Node (Leaf v) tree
    broot = BTree.leaf v ->
    -- We need to be explicit because of the polimophisim of |[] :: List ℍ|
    @containCompute α ℍ _ _ _ v [] broot.hash_BTree
:= by intros HRoot; rw [ containCompute, nodeIn, HRoot, BTree.hash_BTree ]; simp
