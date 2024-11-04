import FraudProof.Games.GameDef -- Players, Winner
import FraudProof.Players

-- Data Structures
import FraudProof.DataStructures.BTree -- Btree
import FraudProof.DataStructures.MTree -- MTree
import FraudProof.DataStructures.Hash -- hash classes

import FraudProof.Extras.BToMTree -- Btree
-- Sequences
import Mathlib.Data.Fin.Tuple.Basic -- Fin.tail

-- * Proposer from Map-Forget-Populate
structure ProposerDef (α ℍ : Type) where
  values : Skeleton -> Option α
  nodeH  : Skeleton -> Option (ℍ × ℍ)

def AddValue {α ℍ : Type} (s : Skeleton) (r : Option α) (o : ProposerDef α ℍ) : ProposerDef α ℍ
 := ⟨ fun s' => if s == s' then r else o.values s', o.nodeH ⟩
def AddNodeH {α ℍ : Type} (s : Skeleton) (r : Option (ℍ × ℍ)) (o : ProposerDef α ℍ) : ProposerDef α ℍ
 := ⟨ o.values, fun s' => if s == s' then r else o.nodeH s' ⟩

-- def fromDataProposer' {α ℍ: Type} (t : ABTree ((α × ℍ) × Skeleton) (ℍ × Skeleton))
--   (acc : ProposerDef α ℍ) : ProposerDef α ℍ
--   := match t with
--     | .leaf ⟨ ⟨ v , _ ⟩ , skl ⟩ => AddValue skl (some v) acc
--     | .node ⟨ _ , skl ⟩ bl br => sorry

-- def fromDataProposer' {α ℍ: Type} (t : ABTree (α × ℍ) ℍ) : ProposerDef α ℍ
--  :=t.InjPath

abbrev ProposerStrategy (α ℍ : Type):= ABTree (Option α) (Option (ℍ × ℍ))

-- How bad people create their strategies? I dunno :shrug:
def simpGoodGen {α ℍ : Type}[o : Hash α ℍ][m : HashMagma ℍ] (t : BTree α) : ProposerStrategy α ℍ
 :=  (@propTree _ _ o m t).map (fun a => some $ a.1) (fun n => some $ n.2 )

def GenProposer {α ℍ : Type} (pdef : ProposerDef α ℍ) (comp : ABTreeSkeleton)
 : ProposerStrategy α ℍ
 := comp.TSkeleton.map pdef.values pdef.nodeH

-- * Chooser
-- Types
-- Using parenthesis to split concepts
abbrev ChooserStrategy (ℍ : Type) := ABTree Unit ((ℍ × ℍ) -> Option ChooserMoves)
-- Options?
abbrev OChooserStrategy (ℍ : Type) := ABTree (Option Unit) ((ℍ × ℍ) -> Option ChooserMoves)

-- Generating Strategies
-- Chooser operates on the assumtion that the top hash is wrong.
-- Otherwise it is not invoked at all.
def GenChooser {ℍ : Type} (cdef : Skeleton -> ((ℍ × ℍ) -> Option ChooserMoves)) (comp : ABTreeSkeleton)
  : ChooserStrategy ℍ
  := comp.TSkeleton.map (fun _ => ()) cdef

-- So, we assume that the A.1:|comb offered.1 offered.2 != gen.1|.
--
def ChooserStr {ℍ : Type}[BEq ℍ] (gen : ℍ × ℍ × ℍ) (offered : ℍ × ℍ ) : Option ChooserMoves
 := match gen , offered with
    | ⟨ _ , gBl , gBr ⟩ , ⟨ ol , or ⟩ =>
      if ol == gBl
      then some .Now -- Because A.1 and hash properties of |comb|, we should challenge here.
      else if or == gBr
           then some .Now
           else some $ .Continue .Left -- It does not matter from the point of
           -- view of correctness but since we know the tree, we can follow the
           -- shortest path.

def simpChooser {α ℍ : Type}[BEq ℍ][Hash α ℍ][HashMagma ℍ] ( t : BTree α ) : ChooserStrategy ℍ
 := (propTree t).map (fun _ => ()) ChooserStr

-- What if I modeled no posible moves as game ending.
-- Adding a checking move as move. | LastElemChk |.
--
-- This is a /semi/ good proposer. Skeletons could be of /wrong size/.
def SemiGoodProposer {α ℍ : Type}
   (data : ABTree (α × ℍ)  ℍ)
   (skl : Skeleton)
   : Option (PMoves ℍ)
   := match skl , data with
   | .nil , .leaf _ => none -- We should not get here
   | .nil , .node _ bl br => some $ .Next ⟨ bl.getI , br.getI ⟩
   | .cons (.inl _) sk , .node _ l _ => SemiGoodProposer l sk
   | .cons (.inr _) sk , .node _ _ r => SemiGoodProposer r sk
   | _ , _ => none

def SemiCompleteProposer {α ℍ : Type}
  (data : ABTree (α × ℍ) ℍ)
  (skl : Skeleton)
  : Option (PMoves' α (ℍ × ℍ))
  := match skl , data with
     | .nil , .leaf v => some $ .End v.1
     | .nil , .node _i bl br => some $ .Next ⟨ bl.getI , br.getI ⟩
     | .cons (.inl _) rs , .node _i b _ => SemiCompleteProposer b rs
     | .cons (.inr _) rs , .node _i _ b => SemiCompleteProposer b rs
     --  Nonsense case, I think. This is a Skeleton longer than the data
     --  A /bad path/. That's why Indexed Trees with shortest path are complete.
     | .cons _ _ , .leaf _=> none

def Proposer {α ℍ : Type}{s m l : Nat}
  (_mLTs : m ≤ s)
  (data : MMTree α ℍ s l)
  (iskl : ISkeleton m)
  : PMoves' α (ℍ × ℍ)
  := match s with
    | 0 => match data with
           | .leaf v _ => .End v
    | .succ _ps =>
      match m with
      | 0 => match data with
             | .node _ _pBot _pTop l r => .Next ⟨ l.getI , r.getI ⟩
      | .succ _pm =>
        -- Head skeleton path
        match iskl ⟨ 0 , by simp ⟩ , data with
        | .inl _ , .node _ _ _ l _ => Proposer (by omega) l (Fin.tail iskl)
        | .inr _ , .node _ _ _ _ r => Proposer (by omega) r (Fin.tail iskl)

-- * Chooser strategy
-- Here we should act under the assumption something is wrong.
-- If the proposed hash is wrong, we should detected.
-- Assuming the hash, that's outised, it is not the one it should be.
def SemiGoodChooser {α ℍ : Type} [BEq ℍ]
  (data : ABTree (α × ℍ) ℍ)
  (skl : Skeleton)
  (pM : ℍ × ℍ)
  : Option ChooserMoves
  := match skl , data with
  -- the only valid hash is |_i| <<-- This is another assumption.
  | .nil , .leaf _v => some .Now
  | .nil , .node _i bl br =>
    if pM.1 == bl.getI ∧ pM.2 == br.getI -- Caught lying!
      then some .Now -- Breakes assumption, remember context hash is /wrong/ [and hash comb is unique.]
    else if pM.1 != bl.getI -- We need to choose branch having a different hash than the one we know.
        then some $ .Continue .Left
        else some $ .Continue .Right
  | .cons (.inl _) sk, .node _i bl _ =>
    SemiGoodChooser bl sk pM
  | .cons (.inr _) sk, .node _i _ br =>
    SemiGoodChooser br sk pM
  -- path is longer than the tree.
  | .cons _ _ , .leaf _ => none

----------------------------------------
-- * Indexed Trees and Paths
-- Function generating a /good proposer/ from a tree, i.e. a proposer winning
-- the game.
def GoodProposer {α ℍ : Type} {m n : Nat}
    ( _mLTn : m < n )
    (data : STree α ℍ n)
    (skl : ISkeleton m)
    --
    :  PMoves ℍ
    := match _Hm : m with
    | 0 => match data with
           | .nodeL _ _ bl br => .Next ⟨ bl.getI , br.getI ⟩
           | .nodeR _ _ bl br => .Next ⟨ bl.getI , br.getI ⟩
    | .succ pm =>
      let fst := skl ⟨ 0 , by simp ⟩
      match fst with
      | .inl _ => match data with
                  | .nodeL _ _ bl _ => GoodProposer (by omega) bl $ Fin.tail skl
                  | .nodeR _ _ bl _ => GoodProposer (by omega) bl $ Fin.tail skl
      | .inr _ => match data with
                  | .nodeL _ _ _ br => GoodProposer (by omega) br $ Fin.tail skl
                  | .nodeR _ _ _ br => GoodProposer (by omega) br $ Fin.tail skl
