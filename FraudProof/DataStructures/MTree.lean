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
-- ** Access
def ABTree.access {α β : Type} (t : ABTree α β)(p : Skeleton) : Option (α ⊕ β)
 := match t , p with
   | .leaf a , .nil => .some $ .inl a
   | .node b _ _ , .nil => .some $ .inr b
   | .node _ bl _ , .cons .Left ps =>  bl.access ps
   | .node _ _ br , .cons .Right ps => br.access ps
   | _ , _ => .none

def ABTree.iaccess {α β : Type}{n : Nat}(t : ABTree α β)(p : ISkeleton n) : Option (α ⊕ β)
  := t.access $ sequence_forget p

lemma ABTree.iaccess_head_left {α β : Type}{n : Nat}{bl br : ABTree α β}{b : β}{p : ISkeleton n.succ} {res : Option (α ⊕ β)}
  : p.head = .Left -> (ABTree.node b bl br).iaccess p = res -> bl.iaccess p.tail = res
  := by
   simp [ABTree.iaccess, sequence_forget]
   have ⟨ pls, plen ⟩ := p
   simp; cases pls
   case nil => simp at plen
   case cons x xs =>
     simp; intro XL; rw [XL]
     simp [Sequence.tail, ABTree.access]

lemma ABTree.iaccess_head_right {α β : Type}{n : Nat}{bl br : ABTree α β}{b : β}{p : ISkeleton n.succ} {res : Option (α ⊕ β)}
  : p.head = .Right -> (ABTree.node b bl br).iaccess p = res -> br.iaccess p.tail = res
  := by
   simp [ABTree.iaccess, sequence_forget]
   have ⟨ pls, plen ⟩ := p
   simp; cases pls
   case nil => simp at plen
   case cons x xs =>
     simp; intro XL; rw [XL]
     simp [Sequence.tail, ABTree.access]

lemma nil_access {α β : Type}(t : ABTree α β)(a : α)
  : t.iaccess .nil = .some (.inl a) ↔ t = .leaf a
  := by
  apply Iff.intro
  · intro Hip; simp [ABTree.iaccess, sequence_forget, ABTree.access ] at Hip
    cases t with
    | leaf w => simp [ABTree.access] at Hip; congr
    | node _ _ _ => simp [ABTree.access] at Hip
  · intro Hip; rw [Hip]; simp [ABTree.iaccess, sequence_forget, ABTree.access]


-- Access dups
--
def no_dup_elements {α : Type}[DecidableEq α](t : BTree α)
 : Prop :=
 forall (p q : Skeleton)(p_v q_v : α),
    ¬ p = q -> t.access p = .some (.inl p_v) -> t.access q = .some (.inl q_v) -> ¬ p_v = q_v

def no_dup_elements_indexed {α : Type}[DecidableEq α](t : BTree α)
 : Prop :=
 forall {n : Nat}(p q : ISkeleton n)(p_v q_v : α),
    ¬ p = q -> t.iaccess p = .some (.inl p_v) -> t.iaccess q = .some (.inl q_v) -> ¬ p_v = q_v
 ∧
 forall {n m : Nat}(p : ISkeleton n)(q : ISkeleton m)(p_v q_v : α),
    ¬ n = m -> t.iaccess p = .some (.inl p_v) -> t.iaccess q = .some (.inl q_v) -> ¬ p_v = q_v

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
