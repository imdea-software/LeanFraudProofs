import FraudProof.DataStructures.BTree
import FraudProof.DataStructures.MTree
import FraudProof.DataStructures.Sequence

import Mathlib.Data.List.Lattice

----------------------------------------
-- ** Access
--
def ABTree.access {α β : Type} (t : ABTree α β)(p : Skeleton) : Option (α ⊕ β)
 := match t , p with
   | .leaf a , .nil => .some $ .inl a
   | .node b _ _ , .nil => .some $ .inr b
   | .node _ bl _ , .cons .Left ps =>  bl.access ps
   | .node _ _ br , .cons .Right ps => br.access ps
   | _ , _ => .none

def ABTree.iaccess {α β : Type}{n : Nat}(t : ABTree α β)(p : ISkeleton n) : Option (α ⊕ β)
  := t.access $ sequence_forget p

-- Access a Tree by a given path of lenght n reaching a value and returning
-- values along the way.
def ABTree.access_path_value {α β : Type}{n : Nat}(t : ABTree α β)(p : ISkeleton n) : Option ( Sequence n β × α )
 := match n, t with
   | 0 , .leaf v => .some (.nil , v)
   | .succ _pn , .node b bl br =>
           ((p.head.destruct bl.access_path_value br.access_path_value) p.tail).map (fun (rs , a) => (rs.cons b, a))
   -- Bad cases?
   | _ , _ => .none

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
  · intro Hip; simp [ABTree.iaccess, sequence_forget ] at Hip
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

lemma path_toPaths_wk {α β : Type}
   {x : SkElem}
   {pr pathTail : Skeleton}
   {t : ABTree α β}
   {e : α ⊕ β}
   (H : (pathTail, e) ∈ t.toPaths' pr)
   : (x :: pathTail, e) ∈ t.toPaths' (x :: pr)
   := by
   revert pr
   induction t with
   | leaf v => simp at *
   | node b bl br HL HR
     => simp at *
        intros pr H
        cases H
        case inl h => left; assumption
        case inr h
          => right
             cases h
             case inl h => left; apply HL
                           assumption
             case inr h => right; apply HR; assumption

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

theorem toPath_are_paths' {α β : Type}(t : ABTree α β)
  : forall (path : Skeleton)( e : α ⊕ β )
  , t.access path = e -> (path, e) ∈ t.toPaths
  := by
  induction t with
  | leaf v
    => simp [ABTree.toPaths]
       intro path
       cases path <;> simp [ABTree.access]
  | node b bl br HinL HinR
    => intros path e HAcc
       cases path with
       | nil => simp [ABTree.access] at HAcc
                simp [ABTree.toPaths]
                left; rw [HAcc]
       | cons p ps
         => cases p with
            | Left => simp [ABTree.access] at HAcc
                      simp [ABTree.toPaths]
                      left
                      apply HinL at HAcc
                      apply path_toPaths_wk
                      assumption
            | Right
              => simp [ABTree.access] at HAcc
                 simp [ABTree.toPaths]
                 right
                 apply HinR at HAcc
                 apply path_toPaths_wk
                 assumption


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

def BTree.toPaths_elems {α : Type}
  : BTree α -> List (Skeleton × α)
  := List.filterMap
      (fun (x : Skeleton × (α ⊕ Unit))
       => match x.snd with
               | .inl v => .some (x.fst, v)
               | .inr _ => none)
      ∘ ABTree.toPaths
  -- (t.toPaths.foldr (fun (skl, e) rs => match e with | .inl v => (skl, v) :: rs | .inr _ => rs) .nil)

lemma paths_elems_are_paths {α : Type}(t : BTree α )(p : Skeleton)(a : α)
  : (p, .inl a) ∈ t.toPaths <-> (p, a) ∈ t.toPaths_elems
  := by cases t with
  | leaf v => simp [ABTree.toPaths,BTree.toPaths_elems]
  | node _ bl br=> simp [ABTree.toPaths, BTree.toPaths_elems]

lemma paths_elems_acc_irreverent {α β : Type}( t : ABTree α β) (al bl : Skeleton)
  : (t.toPaths' al).map (·.snd) = (t.toPaths' bl).map (·.snd)
  := by
  revert al bl
  induction t with
  | leaf v => simp
  | node b tl tr HL HR =>
    intros al bl
    simp
    rw [HL]; rw [HR]

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
    -- congr
    unfold BTree.toPaths_elems
    have lemappend : forall {γ: Type}(y : γ), List.cons y .nil = ([y] ++ List.nil)
        := by simp
    rw [lemappend]; rw [toPaths_append];simp; rw [List.map_filterMap]; simp
    rw [lemappend]; rw [toPaths_append];simp; rw [List.map_filterMap]; simp
    rw [List.map_filterMap]; rw [List.map_filterMap]
    have ft : forall (f : Skeleton -> Skeleton),
      (fun (x : Skeleton × (α ⊕ Unit)) => Option.map (fun x ↦ x.snd)
                (match x.2 with
                | Sum.inl v => some $ (f x.1, v)
                | Sum.inr val => none)) =
        fun x => match x.2 with
         | Sum.inl v => some v
         | Sum.inr _ => none
            := by intro f; funext; rename_i x; cases x.2; all_goals {simp}
    rw [ft]; rw [ft]
    unfold ABTree.toPaths
    have ftid := ft id; simp at ftid
    rw [ftid]

lemma toPaths_elems_skeletons {α : Type}(t : BTree α)
  (a : α)
  (aIn : a ∈ List.map (fun x ↦ x.2) t.toPaths_elems)
  : ∃ (sk : Skeleton), (sk, a ) ∈ t.toPaths_elems
  := by simp at *; assumption

lemma proj_comp {α β γ : Type} (f : α -> γ)
     : (fun (x : γ × β) => x.1) ∘ (fun ((a,b) : α × β) => (f a, b))
     = fun x => f x.1
     := by funext; simp

lemma List.Disjoint.list_cons {α : Type}
      (x y : α)(neq : ¬ x = y)
      (ls rs : List (List α))
      : (List.map (List.cons x) ls).Disjoint (List.map (List.cons y) rs)
      := by
 induction ls with
 | nil => simp
 | cons ls lss HI =>
   simp
   apply And.intro
   · intro _; intro cong; symm at cong; contradiction
   · assumption

lemma diff_head_nodup {α: Type}
     (l_1 l_2 : List (List α))(e_1 e_2 : α)
     (HL : l_1.Nodup) (HR : l_2.Nodup)
     (hneq : ¬ e_1 = e_2)
     : (List.map (List.cons e_1) l_1 ++
      List.map (List.cons e_2) l_2).Nodup
 := by
 apply List.Nodup.append
 · apply List.Nodup.map_on
   simp; assumption
 · apply List.Nodup.map_on
   simp; assumption
 · apply List.Disjoint.list_cons
   assumption

theorem path_different {α β : Type}(t : ABTree α β)
  : List.Nodup (t.toPaths.map (·.fst))
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
     have f : forall {γ : Type}{e : SkElem}, (fun x : Skeleton × γ => e :: x.1) = List.cons e ∘ (·.fst)
       := by intros γ e; funext;simp
     rw [f]
     rw [f]
     rw [<- List.map_comp_map]
     rw [<- List.map_comp_map]
     apply diff_head_nodup
     unfold ABTree.toPaths at HL; assumption
     unfold ABTree.toPaths at HR; assumption
     simp

----------------------------------------
-- Operations on lists.
-- Finding evidence and witnesses.
@[simp]
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


theorem find_first_split_none_wk {α : Type}
   (P : α -> Bool)(els accl accr : List α)
   : find_first_split_acc P els (accl.append accr) = .none
   -> find_first_split_acc P els accr = .none
   := by
   revert accl accr
   induction els with
   | nil => simp [find_first_split_acc]
   | cons hd tl HI =>
     intros accl accr
     simp [find_first_split_acc]
     split
     case isTrue h => simp
     case isFalse h => intro H; apply HI at H; assumption

lemma find_first_split_none_forget{α : Type}
   (P : α -> Bool)(els acc : List α)
   : find_first_split_acc P els [] = .none
   -> find_first_split_acc P els acc = .none
   := by revert acc; induction els with
   | nil => simp
   | cons hd tl HI =>
     intros acc FF
     simp at *
     rw [ite_eq_iff] at FF
     cases FF
     case inl h => simp at h
     case inr h =>
       have ⟨ cF , rest ⟩ := h
       rw [ite_cond_eq_false]
       apply HI
       have connil : [hd] = [hd] ++ [] := by simp
       rw [connil] at rest; apply find_first_split_none_wk at rest
       assumption
       apply eq_false; assumption

theorem find_first_split_none {α : Type}
   (P : α -> Bool)(els acc : List α)
   (HAcc : ∀ e ∈ acc, ¬ P e)
   : find_first_split_acc P els acc = .none
   -> forall (e:α), (e ∈ (els ++ acc)) -> ¬ P e
   := by
   revert acc
   induction els with
   | nil => simp [find_first_split_acc]
   | cons hd tl HI =>
     intros acc HAcc fF
     simp [find_first_split_acc] at fF
     rw [ite_eq_iff] at fF
     simp at fF
     have ⟨ nh ,fF ⟩ := fF
     apply HI at fF
     simp
     apply And.intro
     · assumption
     · intros a aIn
       apply Bool.of_not_eq_true
       apply fF
       simp
       cases aIn
       case inl h => left; assumption
       case inr h => right; left; assumption
     simp
     intros e H
     cases H
     case inl h => apply Bool.of_not_eq_true; apply HAcc;assumption
     case inr h => subst_eqs; assumption

theorem find_first_split_none' {α : Type}
   (P : α -> Bool)(els acc : List α)
   : (forall (e:α), (e ∈ els) -> ¬ P e)
   -> find_first_split_acc P els acc = .none
   := by
   revert acc; induction els with
   | nil => simp
   | cons hd tl HI =>
     intros acc AE
     simp at *
     rw [AE.1]; simp
     apply HI; exact AE.2

theorem find_first_split_acc_law {α : Type}
        (P : α -> Bool)(elems acc pred sect : List α)( e : α )
        : find_first_split_acc P elems acc = .some (pred, e , sect)
        -> (∀ e' ∈ acc, ¬ P e')
        -> acc ++ elems = pred ++ [e] ++ sect ∧ (P e) ∧ ∀ e' ∈ pred, ¬ P e'
        := by
  revert pred sect acc
  induction elems with
  | nil => simp [find_first_split_acc]
  | cons hd tl HI =>
    intros acc pred seccs H NPacc
    simp [find_first_split_acc] at H
    cases Hp : P hd
    case true =>
      rw [Hp] at H; simp at H
      have ⟨ h_1, h_2, h_3⟩ := H
      subst_eqs
      simp at *
      apply And.intro <;> assumption
    case false =>
      rw [Hp] at H; simp at H
      apply HI at H
      conv at H =>
       pattern acc ++ [hd] ++ tl
       simp
      apply H
      intros a aIn
      simp at aIn
      cases aIn
      case inl h => apply NPacc; assumption
      case inr h => rw [h]; simp; assumption

def find_two_pred {α : Type}
    (P : α -> Bool)(elems : List α)
    : Option (List α × α × List α × α × List α)
    := match find_first_split P elems with
       | .none => .none
       | .some (pred, e, ss) =>
          (find_first_split P ss).map ( fun (mid, t, succs) => (pred, e ,mid, t, succs) )

@[simp]
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
      tauto

lemma finds_dups_law_elems {α β : Type}[DecidableEq α] (f : β -> α)
  (elems pred mid succs : List β)
  (e_1 e_2 : β)
  (H : find_dups f elems = .some (pred, e_1, mid, e_2, succs))
  : elems = pred ++ [e_1] ++ mid ++ [e_2] ++ succs
    ∧ f e_1 = f e_2
  := by
  have ff := finds_dups_law_elems_acc f elems [] pred mid succs e_1 e_2
  simp at *; apply ff; unfold find_dups at H; assumption

lemma filtermap_nodup {α : Type}{ t : BTree α}
      (H : ((ABTree.toPaths t).map (·.1)).Nodup)
      : (List.filterMap
        (fun x ↦
          match x.2 with
          | Sum.inl v => some (x.1, v)
          | Sum.inr _val => none)
        (ABTree.toPaths t)).Nodup
      := by
      apply List.Nodup.filterMap
      · simp
      · apply List.Nodup.of_map at H; assumption

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
      ·
        have elem_e_1 : t.toPaths_elems = pred ++ e_1 :: (mid ++ [e_2] ++ succs) :=
           by rw [H.1]; simp
        have getE1 := @List.getElem_of_append _ _ _ _ pred.length _ elem_e_1 rfl
        have elem_e_2 : t.toPaths_elems = (pred ++ [e_1] ++ mid) ++ e_2 :: succs :=
           by rw [H.1]; simp
        have getE2 := @List.getElem_of_append _ _ _ _ (pred ++ [e_1] ++ mid).length _ elem_e_2 rfl
        unfold BTree.toPaths_elems at getE1 getE2
        simp at getE1 getE2
        have HNodup : (List.filterMap
        (fun x ↦
          match x.2 with
          | Sum.inl v => some (x.1, v)
          | Sum.inr val => none)
        (ABTree.toPaths t)).Nodup := by apply filtermap_nodup; assumption
        intro eq
        have heq : e_1 = e_2 := by rw [Prod.eq_iff_fst_eq_snd_eq]; apply And.intro <;> assumption
        simp at *
        rw [<- getE1] at heq
        conv at heq =>
          rhs; rw [<- getE2]
        rw [List.Nodup.getElem_inj_iff HNodup] at heq
        simp at heq
      · assumption

lemma finds_dup_wk' {α β : Type}[DecidableEq α]{f : β -> α}
   (els accl accr : List β)
   : find_dups_acc f els  accr = .none
   -> find_dups_acc f els (accl ++ accr) = .none
   := by revert accl accr; induction els with
   | nil => simp
   | cons hd tl HI =>
     intros accl accr
     simp; intro HF
     split
     case h_1 x heq => rw [heq] at HF; simp at HF; apply HI;assumption
     case h_2 _ _ _ _ heq => rw [heq] at HF; simp at HF

lemma finds_dup_wk {α β : Type}[DecidableEq α]{f : β -> α}
   (els accl accr : List β)
   : find_dups_acc f els (accl ++ accr) = .none
   -> find_dups_acc f els accr = .none
   := by
  revert accl accr
  induction els with
  | nil => simp [find_dups_acc]
  | cons e els HI =>
    intros accl accr
    simp [find_dups_acc]
    split
    case h_1 x heq =>
      intro hep
      apply HI at hep; assumption
    case h_2 _ _ _ _ _ => simp

lemma finds_no_dup {α β : Type}[DecidableEq β]
   (f : α -> β)(elems : List α)
   (no_dups_found : find_dups f elems = .none)
   : List.Nodup (elems.map f)
   := by
   induction elems with
   | nil => simp
   | cons e els HI =>
     simp
     unfold find_dups at no_dups_found
     unfold find_dups_acc at no_dups_found
     simp at no_dups_found
     split at no_dups_found
     case h_1 x heq =>
       apply find_first_split_none at heq
       apply And.intro
       · simp at heq; intros x xIn ff; symm at ff; apply heq at ff; simp at ff; assumption
       · apply HI
         have henil : [e] = [e] ++ [] := by simp
         rw [henil] at no_dups_found
         apply finds_dup_wk at no_dups_found
         unfold find_dups; assumption
       -- proof obl
       simp
     case h_2 x pred e_2 sccs heq => simp at no_dups_found


lemma finds_no_dup_head_forall {α β : Type}[DecidableEq β]
   (f : α -> β)(a : α)(elems : List α)
   (no_dups_found : find_dups f (a :: elems) = .none)
   : ∀ e ∈ elems, ¬ f a = f e
   := by
   apply finds_no_dup at no_dups_found
   simp at no_dups_found
   intros e EIn
   replace no_dups_found := no_dups_found.1 e EIn
   intro fae; apply no_dups_found; symm; assumption

lemma no_dups_no_first_head {α β : Type}[DecidableEq β]
  (f : α -> β)(a : α)(els : List α )
  (h_nodups : find_dups f (a :: els) = .none)
  : find_first_split (fun y => f a == f y) els = .none
  := by
  apply finds_no_dup_head_forall at h_nodups
  unfold find_first_split
  apply find_first_split_none'
  simpa

lemma no_find_dups_head {α β : Type}[DecidableEq β]
  (f : α -> β)(a :α)(elems : List α )
  (h_nodups : find_dups f elems = .none)
  (h_no_elems : ∀ e ∈ elems, ¬ f a = f e)
  : find_dups f (a :: elems) = .none
  := by
  simp [find_dups]
  -- apply find_first_split_none' _ _ [] at h_no_elems
  have ffist := find_first_split_none' (fun x => f a = f x) elems [] (by simp; assumption)
  unfold find_first_split
  have ff_none : find_first_split_acc (fun e ↦ f a == f e) elems [] = none :=
    by exact ffist
  rw [ff_none]; simp
  have connil : [a] = ([a] ++ []) := by {simp}; rw [connil]
  apply finds_dup_wk'; assumption

lemma no_dups_finds_none {α β : Type}[DecidableEq β]
  (f : α -> β)(elems : List α )
  (h_nodups : List.Nodup (elems.map f))
  : find_dups f elems = .none
  := by
  induction elems with
  | nil => simp [find_dups,find_dups_acc]
  | cons hd tl HInd =>
    simp at *
    have ⟨ hl , Htl ⟩ := h_nodups
    apply no_find_dups_head -- <;> assumption
    · apply HInd; assumption
    · intros e EIn; apply hl at EIn; intro ff; apply EIn; symm; assumption

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

---------------------------
-- Intersection
-- def SplitAt (α : Type) : Type := List α × α × List α

def find_first_split_proj {β α : Type}[DecidableEq α]
    (proj : β -> α)(b : β)(ll : List β )
    : Option (List β × β × List β)
    := find_first_split (proj · == (proj b)) ll

lemma split_at_value {β α : Type}[DecidableEq α]{proj : β -> α}
   {b b' : β}{pred ll pos : List β}
   : find_first_split_proj proj b ll = .some (pred, b' , pos)
   -> ll = pred ++ [b'] ++ pos
   ∧ ¬ (proj b ∈ (List.map proj pred))
   ∧ proj b' = proj b
   := by
   unfold find_first_split_proj; unfold find_first_split
   intro Hfind
   let find_law := find_first_split_acc_law (proj . == proj b) ll [] pred pos b'
   apply find_law at Hfind; clear find_law
   simp at Hfind
   apply And.intro
   · simp; apply Hfind.1
   · apply And.intro
     · simp; apply Hfind.2.2
     · apply Hfind.2.1

lemma split_at_none {β α : Type}[DecidableEq α]{proj : β -> α}
   {b : β}{ ls : List β}
   : find_first_split_proj proj b ls = .none
   -> ¬ (proj b) ∈ ls.map proj
   := by
   unfold find_first_split_proj; unfold find_first_split
   intro HfindNone; apply find_first_split_none at HfindNone <;> simp at *
   assumption

-- Find first on first list
def find_intersect' {β α : Type}[DecidableEq α]
    (proj : β -> α)(ll rr acc : List β)
    : Option ((List β × β × List β) × (List β × β × List β))
    := match ll with
      | .nil => .none
      | .cons le les =>
        match find_first_split_proj proj le rr with
        | .none => find_intersect' proj les rr (acc.concat le)
        | .some inter_rr => .some ( (acc, le, les) , inter_rr)

def split_at_first_pred' {α β: Type}
     (pred : α -> Option β) (l acc : List α)
     : Option ((List α × α × List α) × β)
     := match l with
      | .nil => .none
      | .cons le ls =>
        match pred le with
        | .none => split_at_first_pred' pred ls (acc.concat le)
        | .some b => .some ((acc , le , ls), b)

lemma split_at_first_pred'_none {α β : Type}
     {pred : α -> Option β} {l acc : List α}
     (H : split_at_first_pred' pred l acc = .none)
     : ∀ a ∈ l, pred a = .none
     := by
     revert acc
     induction l with
     | nil => simp
     | cons y ys IH =>
      intros acc H
      simp; simp [split_at_first_pred'] at H
      cases Hy : pred y with
      | none => simp [*] at *; apply IH at H; assumption
      | some v => simp [*] at *

lemma none_split_at_first_pred' {α β : Type}
     {pred : α -> Option β} {l acc : List α}
     (H : ∀ a ∈ l, pred a = .none)
     : split_at_first_pred' pred l acc = .none
     := by
     revert acc
     induction l with
     | nil => simp [split_at_first_pred']
     | cons y ys IH
      => simp [split_at_first_pred']
         intro acc
         cases Hy : pred y with
         | some b => simp at H; simp [*] at *
         | none => simp; apply IH; simp [*] at *; assumption

lemma split_eq_value {α β : Type}
    {pred : α -> Option β}{a : α}{b : β}{l acc ls rs : List α}
    (HSome : split_at_first_pred' pred l acc = ((ls, a, rs) , b ))
    : pred a = .some b
    := by
    revert acc
    induction l with
    | nil => simp [split_at_first_pred']
    | cons y ys HI =>
      simp [split_at_first_pred']
      intro acc
      cases HC : pred y with
      | none =>
         simp at *
         apply HI
      | some y' =>
         simp
         intros h1 h2 h3 h4; subst_eqs; assumption

lemma split_at_first_pred'_some{α β: Type}
     {pred : α -> Option β}{a : α}{b : β} {l acc ls rs: List α}
     (H : split_at_first_pred' pred l acc = .some ((ls, a , rs), b))
     : acc ++ l = ls ++ a :: rs
     := by
     revert acc
     induction l with
     | nil => simp [split_at_first_pred']
     | cons y ys IH =>
      simp [split_at_first_pred']
      cases HP : pred y with
      | none =>
        simp
        intros acc; replace IH := @IH (acc ++ [y])
        simp at IH; assumption
      | some v =>
        simp; intros; subst_eqs; tauto

def split_at_first_pred {α β: Type}
     (pred : α -> Option β) (l : List α)
     : Option ((List α × α × List α) × β)
     := split_at_first_pred' pred l .nil

-- lemma splitAtFirstLaw {α β : Type}
--       {pred : α -> Option β}{ls pre pos : List α}{a : α}{rs : β}
--       (H : split_at_first_pred pred ls = .some ((pre,a,pos), rs))
--       : ls = pre ++ [a] ++ pos
--       ∧ pred a = .some rs
--       := sorry

lemma splitAtFirstNone {α β : Type}
     {pred : α -> Option β}{ls : List α}
     (H : split_at_first_pred pred ls = .none)
     : ∀ a ∈ ls, pred a = .none
     := by unfold split_at_first_pred at H; apply split_at_first_pred'_none at H; assumption

lemma splitAtFirstNone' {α β : Type}
     {pred : α -> Option β}{ls : List α}
     (H : ∀ a ∈ ls, pred a = .none)
     : split_at_first_pred pred ls = .none
     := by unfold split_at_first_pred; apply none_split_at_first_pred'; assumption

def find_intersect {β α : Type}[DecidableEq α]
    (proj : β -> α)(ll rr : List β)
    : Option ((List β × β × List β) × (List β × β × List β))
    := split_at_first_pred (find_first_split_proj proj · rr) ll


lemma find_intersect_law {β α : Type}[DecidableEq α]{proj : β -> α}
      (ls prels posls rs prers posrs : List β)
      (el er : β)
      (H : find_intersect proj ls rs = .some ( (prels, el, posls), (prers, er, posrs)))
      : ls = prels ++ [el] ++ posls
      ∧ rs = prers ++ [er] ++ posrs
      ∧ proj el = proj er
      -- ∧ ∀ a ∈ prels, ∀ b ∈ prers, ¬ proj a = proj b -- We do not need it for the proof
      := by
      unfold find_intersect at H; unfold split_at_first_pred at H
      have HList := split_at_first_pred'_some H
      have HVal := split_eq_value H
      apply split_at_value at HVal
      apply And.intro
      · simp at HList; simp;assumption
      apply And.intro
      · simp [*]
      · simp [*]

lemma find_intersect_none {β α : Type}[DecidableEq α]{proj : β -> α}
      {ls rs : List β}
      (H : find_intersect proj ls rs = .none)
      : ∀ l ∈ ls, ∀ r ∈ rs, ¬ proj l = proj r
      := by
      unfold find_intersect at H; unfold split_at_first_pred at H
      have HP := split_at_first_pred'_none H
      intros l lInls r rInrs
      have HR := HP l lInls
      apply split_at_none at HR
      simp at HR
      replace HR := HR r rInrs
      intro F; apply HR; simp [*]



lemma find_intersect_none' {β α : Type}[DecidableEq α]{proj : β -> α}
      {ls rs : List β}
      (H : ∀ l ∈ ls, ∀ r ∈ rs, ¬ proj l = proj r)
      : find_intersect proj ls rs = .none
      := by
      unfold find_intersect; unfold split_at_first_pred
      apply none_split_at_first_pred'
      unfold find_first_split_proj
      intros a aIn
      unfold find_first_split
      apply find_first_split_none'
      intros r rIn
      simp; intro F; apply H; assumption; assumption; simp [*]
---------------------------
