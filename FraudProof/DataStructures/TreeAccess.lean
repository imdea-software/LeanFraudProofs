import FraudProof.DataStructures.BTree
import FraudProof.DataStructures.MTree
import FraudProof.DataStructures.Sequence


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

lemma access_iaccess {α β : Type}(t : ABTree α β)(p : Skeleton)
    : t.access p = t.iaccess (sequence_lift p)
    := by simp [ABTree.iaccess, sequence_lift,sequence_forget]

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


----------------------------------------
-- ** Duplicate Elements in Trees.
--
-- Straight search. Different Elements at all possible positions.
def no_dup_elements {α : Type}[DecidableEq α](t : BTree α)
 : Prop :=
 forall (p q : Skeleton)(p_v q_v : α),
    ¬ p = q -> t.access p = .some (.inl p_v) -> t.access q = .some (.inl q_v) -> ¬ p_v = q_v

-- Search by discriminating by dup at same level or diff.
-- In balanced trees, this def may be useful. RN it is not.
def no_dup_elements_indexed {α : Type}[DecidableEq α](t : BTree α)
 : Prop :=
 forall {n : Nat}(p q : ISkeleton n)(p_v q_v : α),
    ¬ p = q -> t.iaccess p = .some (.inl p_v) -> t.iaccess q = .some (.inl q_v) -> ¬ p_v = q_v
 ∧
 forall {n m : Nat}(p : ISkeleton n)(q : ISkeleton m)(p_v q_v : α),
    ¬ n = m -> t.iaccess p = .some (.inl p_v) -> t.iaccess q = .some (.inl q_v) -> ¬ p_v = q_v

def no_dup_path_elems {α : Type}(t : BTree α)
  : Prop := List.Nodup t.toList

----------------------------------------
-- ** Tree to Path Decomposition
--
@[simp]
def BTree.toPaths' {α : Type}(t : BTree α) (acc : Skeleton) : List (Skeleton × α)
 := match t with
   | .leaf v => [(acc , v)]
   | .node bl br
     => bl.toPaths' (List.concat acc .Left)
     ++ br.toPaths' (List.concat acc .Right)

@[simp]
def ABTree.toPaths' {α β : Type}(t : ABTree α β)(path : Skeleton) : List (Skeleton × (α ⊕ β))
 := match t with
   | .leaf v => [(path , .inl v)]
   | .node b bl br
     => (path , .inr b)
     :: bl.toPaths' (List.concat path .Left)
     ++ br.toPaths' (List.concat path .Right)

lemma concat_prefix {α : Type} (ls et rs : List α)
  : ls.append et <+: rs -> ls <+: rs
  := by
    revert et rs
    induction ls with
    | nil => simp
    | cons l ls HI =>
      simp; intros et rs H
      cases rs with
      | nil => simp at H
      | cons r rs =>
        simp at H; simp
        apply And.intro
        · exact H.1
        · have hi := HI et rs; apply hi; exact H.2

lemma toPaths'_lists_prefix {α β : Type}(t : ABTree α β)(p : Skeleton)
  : forall (path : Skeleton)(e : α ⊕ β), (path, e ) ∈ t.toPaths' p ->
    p <+: path
  := by
  revert p
  induction t with
  | leaf v => simp
  | node b bl br HL HR =>
    intros p path e
    simp; intro ass
    cases ass
    case inl h => rw [h.1];simp
    case inr h =>
        cases h
        case inl isInL =>
          apply HL at isInL
          apply concat_prefix at isInL
          assumption
        case inr isInR =>
          apply HR at isInR; apply concat_prefix at isInR
          assumption

lemma toPaths_append {α β : Type}
   (acc_p acc_q: Skeleton) (t : ABTree α β)
   : t.toPaths' (acc_p ++ acc_q) = ((t.toPaths' acc_q).map (fun (ps, e) => (acc_p ++ ps, e)))
   := by
   revert acc_p acc_q
   induction t with
   | leaf v => simp
   | node b bl br HL HR =>
     intro acc_p acc_q
     simp
     have HLi := HL acc_p (acc_q ++ [.Left])
     have HRi := HR acc_p (acc_q ++ [.Right])
     rw [HLi, HRi]

lemma path_toPaths' {α β : Type}
   {x : SkElem}
   {pathTail : Skeleton}
   {t : ABTree α β}
   {e : α ⊕ β}
   (HR : (x :: pathTail, e) ∈ t.toPaths' [x])
   : (pathTail, e) ∈ t.toPaths' []
   := by
   have toP := toPaths_append [x] [] t; simp at toP
   rw [toP] at HR
   simp at HR
   assumption

-- fromPath (toPaths t) = t (not every from paths forms a tree. Leaves (diff paths) yes tho.)
def ABTree.toPaths {α β : Type}(t : ABTree α β) : List (Skeleton × (α ⊕ β))
 := t.toPaths' .nil

theorem toPath_are_paths {α β : Type}(t : ABTree α β)
  : forall (path : Skeleton)( e : α ⊕ β )
  , (path, e) ∈ t.toPaths -> t.access path = e
  := by
  induction t with
  | leaf v =>
    simp [ABTree.toPaths, ABTree.access]
  | node b bl br HindL HindR =>
    simp
    intro path
    apply And.intro
    · intros a isIn
      simp [ABTree.toPaths] at isIn
      cases isIn
      case inl HL =>
        have hpath := toPaths'_lists_prefix bl [SkElem.Left] path (.inl a) HL
        cases path with
        | nil => simp at hpath
        | cons hd pathTail =>
          simp at hpath
          rw [<- hpath]
          simp [ABTree.access]
          apply HindL
          simp [ABTree.toPaths]
          rw [<- hpath] at HL
          apply path_toPaths' at HL; assumption
      case inr HR =>
        have hpath := toPaths'_lists_prefix br [SkElem.Right] path _ HR
        cases path with
        | nil => simp at hpath
        | cons hd pathTail =>
          simp at hpath
          rw [<- hpath]
          simp [ABTree.access]
          apply HindR
          simp [ABTree.toPaths]
          rw [<- hpath] at HR
          apply path_toPaths' at HR; assumption
    · intros e isIn
      simp [ABTree.toPaths] at isIn
      cases isIn
      case inl x =>
        have ⟨ pathE , eqB ⟩ := x
        subst_eqs
        simp [ABTree.access]
      case inr x =>
        cases x
        case inl h =>
          have Hpre := toPaths'_lists_prefix bl [SkElem.Left] path _ h
          cases path with
          | nil => simp at Hpre
          | cons hd tail =>
            simp at Hpre
            subst_eqs
            simp [ABTree.access]
            apply path_toPaths' at h
            apply HindL; unfold ABTree.toPaths; assumption
        case inr h =>
          have Hpre := toPaths'_lists_prefix br [SkElem.Right] path _ h
          cases path with
          | nil => simp at Hpre
          | cons hd tail =>
            simp at Hpre
            subst_eqs
            simp [ABTree.access]
            apply path_toPaths' at h
            apply HindR; unfold ABTree.toPaths; assumption

def BTree.toPaths_elems {α : Type}(t : BTree α)
  : List (Skeleton × α)
  := (t.toPaths.foldr (fun (skl, e) rs => match e with | .inl v => (skl, v) :: rs | .inr _ => rs) .nil)

lemma path_elems_eq {α : Type}(t : BTree α)
  : List.filterMap (fun (p, e) => match e with | .inl v => some (p,v) | .inr _ => none ) t.toPaths
  = t.toPaths_elems
  := sorry
lemma paths_elems_are_paths {α : Type}(t : BTree α )(p : Skeleton)(a : α)
  : (p, .inl a) ∈ t.toPaths <-> (p, a) ∈ t.toPaths_elems
  := sorry

theorem toPath_elems {α : Type}(t : BTree α)
  : List.map (·.snd) t.toPaths_elems
  = t.toList
  := by
  induction t with
  | leaf _v => simp [BTree.toPaths_elems,ABTree.toPaths, BTree.toList, List.singleton]
  | node _b bl br HL HR =>
    simp [BTree.toPaths_elems,ABTree.toPaths, BTree.toList]
    unfold BTree.toList at HL HR
    rw [abfold_bfold _ _ bl] at HL
    rw [abfold_bfold _ _ br] at HR
    rw [<- HL, <- HR]
    rw [<- List.map_append]
    congr
    unfold BTree.toPaths_elems
    simp
    rw [<- List.foldr_append]
    sorry

lemma proj_comp {α β γ : Type}
     (f : α -> γ)
     : (fun (x : γ × β) => x.1) ∘ (fun ((a,b) : α × β) => (f a, b))
     = fun x => f x.1
     := by funext; simp

lemma diff_head_nodup {α: Type}
     (l_1 l_2 : List (List α))(e_1 e_2 : α)
     (HL : l_1.Nodup) (HR : l_2.Nodup)
     (hneq : ¬ e_1 = e_2)
     : (List.map (List.cons e_1) l_1 ++
      List.map (List.cons e_2) l_2).Nodup
 := sorry

theorem path_different {α β : Type}(t : ABTree α β)
  : List.Nodup (t.toPaths.map (fun (p,e) => p))
  := by
  induction t with
  | leaf v => simp [ABTree.toPaths]
  | node b bl br HL HR =>
   simp [ABTree.toPaths]
   apply And.intro
   · apply And.intro
     · apply And.intro
       all_goals {
         intros x H
         have hl := toPaths_append [.Left] [] bl
         simp at hl; rw [hl] at H
         simp at H
       }
     · apply And.intro
       all_goals {
         intros x H
         have hr := toPaths_append [.Right] [] br
         simp at hr; rw [hr] at H
         simp at H
       }
   · have hl := toPaths_append [.Left] [] bl; simp at hl; rw [hl]
     simp
     have hr :=  toPaths_append [.Right] [] br; simp at hr; rw [hr]
     simp
     rw [proj_comp]
     rw [proj_comp]
     simp at HL; simp at HR
     have f : forall {γ : Type}{e : SkElem}, (fun x : Skeleton × γ => e :: x.1) = List.cons e ∘ (·.fst) := sorry
     rw [f]
     rw [f]
     rw [<- List.map_comp_map]
     rw [<- List.map_comp_map]
     apply diff_head_nodup
     unfold ABTree.toPaths at HL; assumption
     unfold ABTree.toPaths at HR; assumption
     simp

def find_first_split_acc {α : Type}(pred : α -> Bool)(elems : List α)(acc : List α)
  : Option (List α × α × List α)
  := match elems with
    | .nil => .none
    | .cons e els =>
      if pred e then .some (acc, e , els)
      else find_first_split_acc pred els (acc.concat e)

def find_first_split {α : Type}(P : α -> Bool)(elems : List α)
  : Option (List α × α × List α)
  := find_first_split_acc P elems []

theorem find_first_split_acc_law {α : Type}
        (P : α -> Bool)(elems acc pred sect : List α)( e : α )
        : find_first_split_acc P elems acc = .some (pred, e , sect)
        -> acc ++ elems = pred ++ [e] ++ sect ∧ (P e)
        := by
  revert pred sect acc
  induction elems with
  | nil => simp [find_first_split_acc]
  | cons hd tl HI =>
    intros acc pred seccs  H
    simp [find_first_split_acc] at H
    cases Hp : P hd
    case true =>
      rw [Hp] at H; simp at H
      have ⟨ h_1, h_2, h_3⟩ := H
      subst_eqs
      simp
      assumption
    case false =>
      rw [Hp] at H; simp at H
      apply HI at H
      simp at *; assumption

def find_two_pred {α : Type}
    (P : α -> Bool)(elems : List α)
    : Option (List α × α × List α × α × List α)
    := match find_first_split P elems with
       | .none => .none
       | .some (pred, e, ss) =>
          (find_first_split P ss).map ( fun (mid, t, succs) => (pred, e ,mid, t, succs) )

-- def find_dups_extra {α : Type}[DecidableEq α](e : ?) (elems : List α)
--    : Option (List α × α × List α × α × List α)
--    := sorry

-- lemma find_dups_extra_law
--    : finds_dups_extra ts = (pre , e_1 , mid , e_2, pos) -> ts = pre ++ [e_1] ++ mid ++ [e_2] ++ pos
--    := sorry

def find_dups_acc {β α : Type}[DecidableEq α](f : β -> α) (elems acc : List β)
   : Option (List β × β
            × List β × β
            × List β)
   := match elems with
     | .nil => .none
     | .cons e_1 els =>
        match find_first_split (fun e => f e_1 == f e) els with
         | .none => find_dups_acc f els (acc.concat e_1)
         | .some (mid, e_2, succs) => .some (acc, e_1, mid, e_2, succs)

def find_dups{α β: Type}[DecidableEq α] (f : β -> α) (elems : List β)
   : Option (List β × β
            × List β × β
            × List β)
   := find_dups_acc f elems .nil

lemma finds_dups_law_elems_acc {α β : Type}[DecidableEq α] (f : β -> α)
  (elems acc pred mid succs : List β)
  (e_1 e_2 : β)
  (H : find_dups_acc f elems acc = .some (pred, e_1, mid, e_2, succs))
  : acc ++ elems = pred ++ [e_1] ++ mid ++ [e_2] ++ succs
   ∧ f e_1 = f e_2
  := by
  revert acc pred mid succs e_1 e_2
  induction elems with
  | nil => simp [find_dups_acc]
  | cons e els HI =>
    unfold find_dups_acc ; simp
    intros acc pred mid succs e_1 e_2
    split
    case h_1 x heq =>
      intro rec
      apply HI at rec
      simp at *; assumption
    case h_2 r ps e' ss heq =>
      intro res; simp at res
      have ⟨ hpred, he1, hmid, he2, hres ⟩ := res
      apply find_first_split_acc_law at heq
      subst_eqs
      simp at *
      assumption

lemma finds_dups_law_elems {α β : Type}[DecidableEq α] (f : β -> α)
  (elems pred mid succs : List β)
  (e_1 e_2 : β)
  (H : find_dups f elems = .some (pred, e_1, mid, e_2, succs))
  : elems = pred ++ [e_1] ++ mid ++ [e_2] ++ succs
    ∧ f e_1 = f e_2
  := by
  have ff := finds_dups_law_elems_acc f elems [] pred mid succs e_1 e_2
  simp at *; apply ff; unfold find_dups at H; assumption

lemma finds_dups_law_elem_sk {α : Type}[DecidableEq α]
  (t : BTree α)
  --
  {pred mid succs : List (Skeleton × α)}
  (e_1 e_2 : Skeleton × α)
  --
  (H : find_dups (·.snd) t.toPaths_elems = .some (pred, e_1, mid, e_2, succs))
  : t.access e_1.1 = .some (.inl e_1.2)
  ∧ t.access e_2.1 = .some (.inl e_2.2)
  ∧ ¬ e_1.1 = e_2.1
  ∧ e_1.2 = e_2.2
  := by
  apply finds_dups_law_elems at H
  have ⟨ elems , hproj ⟩ := H
  have diff_paths := path_different t; simp at diff_paths
  apply And.intro
  · apply toPath_are_paths
    unfold BTree.toPaths_elems at elems; simp at elems
    rw [paths_elems_are_paths]
    rw [H.1]
    simp
  · apply And.intro
    · apply toPath_are_paths
      rw [paths_elems_are_paths]
      rw [H.1]
      simp
    · apply And.intro
      · sorry
      · assumption

lemma finds_no_dup {α β : Type}[DecidableEq β]
   (f : α -> β)(elems : List α)
   (no_dups_found : find_dups f elems = .none)
   : List.Nodup (elems.map f)
   := sorry

lemma no_dups_finds_none {α β : Type}[DecidableEq β]
  (f : α -> β)(elems : List α )
  (h_nodups : List.Nodup (elems.map f))
  : find_dups f elems = .none
  := sorry

lemma finds_no_dup_inj {α β : Type}
     [DecidableEq β]
     (f : α -> β) -- This makes dec_eq α too
     (elems : List α)
     (H_nodups : find_dups f elems = .none)
     : List.Nodup elems
     := by
     apply finds_no_dup at H_nodups
     apply List.Nodup.of_map
     assumption

-- lemma find_dups_mem {α : Type}[DecidableEq α]
--       (elems : List (Skeleton × α))
--       (res : DuplicateElem α)
--       ( h : find_dups elems = .some res )
--       : (res.path_1 , res.val) ∈ elems ∧ (res.path_2 , res.val) ∈ elems
--       := sorry -- should be easy to prove, it should be in Mathlib

-- theorem find_dups_tree {α β : Type}
--   [DecidableEq α] [DecidableEq β]
--   (t : ABTree α β)
--   (res : DuplicateElem (α ⊕ β))
--   : find_dups t.toPaths = .some res -> ¬ res.path_1 = res.path_2
--   := by
--   have ⟨ p1, p2 , val ⟩ := res
--   simp; intro HFdups
--   have pIn_1 : (p1,val) ∈ t.toPaths := sorry
--   have pIn_2 : (p2,val) ∈ t.toPaths := sorry
