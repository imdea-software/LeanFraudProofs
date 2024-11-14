-- This module serves as the root of the `FraudProof` library.
-- Import modules here that should be built as part of the library.

-- Data Structures
-- import FraudProof.DataStructures.Value
import FraudProof.DataStructures.Hash
import FraudProof.DataStructures.BTree
import FraudProof.DataStructures.MTree

-- Players Def
import FraudProof.Players
import FraudProof.Winning.Proposer -- ( Winning Strategy definitions for proposers. )
import FraudProof.Winning.Chooser -- ( Winning Strategy defs for choosers . )

-- Games Definitions
import FraudProof.Games.GameDef -- ( Winner )

-- Games
import FraudProof.Games.OneStepGame
import FraudProof.Games.LinearGame
import FraudProof.Games.LogGame

-- Computational Tree Games (DAs)
import FraudProof.Games.Base.FromBtoMTree
import FraudProof.Players.FromBToMTree
import FraudProof.Extras.BToMTree

-- Element in Tree
import FraudProof.Games.Base.ElemInTree
import FraudProof.Players.ElemInTree

import Batteries.Data.Fin.Lemmas

namespace LinearGame
-- * Good Proposer winss Linear Game

open Proposer
open WinningProposer
open BotUpLin

-- Hashes type
variable {ℍ : Type}

-- ** /Good
theorem GChalWinsHtoLHashes [BEq ℍ][LawfulBEq ℍ][HashMagma ℍ](gameLength : Nat) :
    forall
    (headH lastH : ℍ)
    (proposer : PropHash gameLength headH lastH)
    (chooser : Chooser.Player ℍ),
    InitHashPathGameHeadToLast gameLength proposer.pathLenNZ headH lastH proposer.strategies chooser = Player.Proposer
    := by
    induction gameLength with
    | zero => -- Impossible
      intros _ _ proposer _
      cases proposer with
      | mk pathLen _ _ _ _ => simp at pathLen
    | succ pn HN =>
      intros hv hr A D
      unfold InitHashPathGameHeadToLast
      unfold HashPathCheckBack
      simp
      cases pn with
      | zero => simp; have ep := @GCLemmas.GChalOneH _ _ hv hr A; rw [ ep ]
      | succ n =>
        simp
        cases D.strategy hv (A.strategies.pathNode ⟨ (n + 1), _ ⟩) hr with
        | Left =>
          simp
          unfold InitHashPathGameHeadToLast at HN
          have HI := HN hv ((A.strategies.pathNode ⟨n + 1, by simp⟩)) (GCShifts.DropLast _ hv hr A) D
          unfold GCShifts.DropLast at HI
          simp at HI
          have eqDropNode := DropLastNodeEq ℍ A.strategies
          have eqDropSib := DropLastSibEq ℍ A.strategies
          have eqInj := HashPathFunInj (by simp) (n + 1) (by simp) (by simp) (DropLastHC ℍ A.strategies) A.strategies ( by rw [Fin.forall_iff]; exact eqDropNode ) ( by rw [Fin.forall_iff] ; exact eqDropSib ) D hv (A.strategies.pathNode ⟨ n+1 , by simp ⟩ )
          rw [ <- eqInj ]
          assumption
        | Right =>
          simp
          have aroot := A.nodeRoot
          simp at aroot
          have agames := A.allGames
          simp at agames
          have lastGame := agames (n + 1) ( by simp )
          clear agames
          rw [ aroot ] at lastGame
          rw [ <- lastGame ]

theorem GChalWinsHtoL {α ℍ : Type}
      [BEq ℍ][LawfulBEq ℍ]
      [m : Hash α ℍ][HashMagma ℍ]
      (gameLength : Nat)
      (v : α) (mt : MTree ℍ)
      (proposer : WinningProposer.WinningProp gameLength v mt)
      (chooser : Chooser.Player ℍ)
      : InitHashPathGameHeadToLast gameLength proposer.pathLenNZ (m.mhash v) mt.hash proposer.strategies chooser = Player.Proposer
      := GChalWinsHtoLHashes gameLength (m.mhash v) mt.hash proposer chooser

  -- We cannot recover witnesses, because Lean has proof irrelevance hardcoded.
  -- theorem KWinsHtoL ( v : Value ) ( tree : BTree Value ) (vInTree : valueIn v tree)
  --   : let ⟨ path , pPath ⟩ := valueInToProof v tree vInTree
  --   exists (proposer : WinningProposer.WinningProp path.length v _),
  --     _Game = Player.Proposer

theorem WinningProposer
    {α ℍ : Type}
    [BEq α][LawfulBEq α]
    [m : Hash α ℍ][HashMagma ℍ]
    [BEq ℍ][LawfulBEq ℍ]
    ( v : α ) ( btree : BTree α )
    (path : TreePath α) (pathNNil : 0 < path.length)
    ( vInBTree : valueInProof v btree = some path)
: forall (chooser : Chooser.Player ℍ),
  have winprop := @Build.WProposerCreate ℍ α _ _ _ _ v btree path pathNNil vInBTree
  InitHashPathGameHeadToLast path.length pathNNil (m.mhash v) (hash_BTree btree).hash winprop.strategies chooser = Player.Proposer
:=  by
  intros ch wp
  exact GChalWinsHtoL path.length v _ wp ch

end LinearGame


namespace LogGame
-- * Good Proposer wins Logarithmic Game

open Proposer
open WinningProposer

variable {ℍ : Type}

-- Predicate to do induction over.
@[simp]
def LogWinningProp' [BEq ℍ][HashMagma ℍ] (gL : Nat) : Prop :=
    forall
    (headH lastH : ℍ)
    (proposer : PropHash gL headH lastH)
    (chooser : Chooser.Player ℍ),
    MembershipGame_2STG gL
    proposer.strategies chooser
    proposer.pathLenNZ -- path is not Zero
    headH lastH = Player.Proposer

theorem PropHashWins [heq : BEq ℍ][LawfulBEq ℍ][mhash : HashMagma ℍ](gL : Nat)
  : @LogWinningProp' ℍ heq mhash gL
  := @Nat.case_strong_induction_on LogWinningProp' gL
     ( -- Empty base case
     by simp
        intros _ _ P _
        have NZ := P.pathLenNZ
        simp at NZ
     )
     ( -- Ind Case
     by intros n SInd
        simp at *
        intros hashB hashT
        intros proposer chooser
        unfold MembershipGame_2STG
        simp
        cases n with
        -- One Step Game, game length = 1.
        | zero =>
               simp
               exact WinningOne proposer
        -- Game length > 1, generating hash and choosing.
        | succ pn =>
          simp
          cases chooser.strategy hashB (proposer.strategies.pathNode ⟨pn / 2 + 1, _ ⟩) hashT with
          | Left => simp
                    let leftWinning := GCOps.take_proposer (pn / 2 + 1) pn.succ.succ (by simp) (by omega) proposer
                    exact SInd (pn / 2 + 1) (by simp; exact Nat.div_le_self pn 2 ) hashB (proposer.strategies.pathNode ⟨pn / 2 + 1, by omega⟩) leftWinning chooser
          | Right => simp
                     let rightWinning := GCOps.drop_proposer (pn / 2 + 1)  pn.succ.succ (by omega) proposer
                     exact SInd (pn + 1 + 1 - (pn / 2 + 1)) (by omega) (proposer.strategies.pathNode ⟨pn / 2 + 1, by omega⟩) hashT rightWinning chooser
     )
end LogGame


namespace LosingProposer
-- Small module to start reasoning about bad proposers.
-- Not necessarily winning choosers.
open Proposer

variable {ℍ : Type}
-- One of the properties making /good/ proposers does no hold.
--
def notZero [BEq ℍ](gl : Nat) (P : HC ℍ gl)(hZ : ℍ) : Prop := P.pathNode ⟨ 0 , by simp ⟩ != hZ
def notRoot [BEq ℍ](gl : Nat) (P : HC ℍ gl)(hR : ℍ) : Prop := P.pathNode ⟨ gl , by simp ⟩ != hR
def notAllGames [BEq ℍ][HashMagma ℍ](gl : Nat)(P : HC ℍ gl) : Prop :=
  exists (p : Nat)(pRange : p < gl),
    P.pathNode ⟨ p + 1 ,  by simp; assumption ⟩ != opHash (P.pathNode ⟨ p , by omega ⟩ ) (P.pathSib ⟨ p , pRange ⟩)

-- Losing proposer is a /bad/ proposer.
-- Bad Proposers fails on (at least) one of the following props:
-- + notZero, initial hash is not correct.
-- + notRoot, final hash is not correct.
-- + there is one hash along the way that does not match up: exists p, node[p+1] = node[p] ⊕ sib[p]
--
def BadProposer [BEq ℍ][HashMagma ℍ]{ gl : Nat } (P : HC ℍ gl) ( hb ht : ℍ ) : Prop
    := notZero gl P hb
    ∨ notRoot gl P ht
    ∨ notAllGames gl P
    ∨ gl = 0 -- HC 0 is empty

-- This depends on the game we are playing.
-- If we want to have a theorem like the following one, we need to think a bit
-- better our hypotheses.
--
-- theorem losingLin
--   ( gameLength : Nat) (gNZ : 0 < gameLength)
--   (hinit hroot : Hash)
--   (P : HC gameLength)
--   (C : Chooser.Player)
--   : BotUpLin.InitHashPathGameLastToHead gameLength gNZ hinit hroot P C = Player.Chooser
--   -> notZero gameLength P hinit
--   ∨ notRoot gameLength P hroot
--   ∨ notAllGames gameLength P

end LosingProposer

namespace WinningChooser

-- If Proposer is /not good/ then, a /knowing chooser/ can wins.
-- The intuition of what a /not good/ proposer can be is 'developed' in the
-- previous namespace.

open BotUpLin

variable {ℍ : Type}
-- The following theorem is to prove that
-- If we know a path of length |gameLength| from |hbot| to |lastH|, |know :Knowing.PathProof gameLength hbot lastH|,
-- we can build a chooser to play the game, if the proposer proposed a wrong initial hash |headH|.

-- This theorem is tighter than the other one. It says (when built with the proper arguments)
-- that the skeleton path proposed by the proposer leads to another value (from the root.)
theorem ChooserGLHeadWrongSeq
    [BEq ℍ][LawfulBEq ℍ] [HashMagma ℍ][SLawFulHash ℍ]
    (gameLength : Nat) (glNZ : 0 < gameLength) :
    forall
    (headH lastH : ℍ)
    (hbot : ℍ )
    (proposer : Proposer.HC ℍ gameLength)
    --
    (_hNEQ : headH != hbot )
    --
    (knowFrom : Knowing.PathProofSeq gameLength (SeqForget proposer.pathSib) hbot lastH)
    ,
    HashPathDrop gameLength glNZ proposer (KnowingLinChooserSkl gameLength knowFrom) headH lastH
    = Player.Chooser
    := by
    induction gameLength with
    | zero => simp at glNZ -- imp case
    | succ pn HInd =>
      intros headH lastH hbot proposer headNEqbot K
      unfold HashPathDrop
      cases pn with -- two cases depending where in the path we are.
      | zero => simp; have gP := K.goodPath; simp at *
                rw [ Fin.foldl_succ , Fin.foldl_zero] at gP
                match Hp0 : proposer.pathSib 0 with
                  | Sum.inl x => rw [ Hp0 ] at gP; simp at gP; rw [ <- gP ]
                                 apply opHash_neqRight
                                 assumption
                  | Sum.inr x => rw [ Hp0 ] at gP; simp at gP; rw [ <- gP ]
                                 apply opHash_neqLeft
                                 assumption
      | succ ppn =>
        simp [ KnowingLinChooserSkl ] at *
        cases hkC : LinChooser (Knowing.inPathSeq 0 _ K) (Knowing.inPathSeq 1 _ K) headH (proposer.pathNode 1) with
          | Left => simp; simp [LinChooser] at hkC
                    have hbB
                    : ¬ headH = Knowing.inPathSeq 0 (by simp) K
                    := by simpa [ Knowing.inPathSeq ]
                    rw [ ite_cond_eq_true ] at hkC
                    simp at hkC
                    unfold Knowing.inPathSeq at hkC; rw [ Fin.foldl_succ, Fin.foldl_zero ] at hkC
                    rw [ hkC ]
                    simp
                    match proposer.pathSib 0 with

| Sum.inl x =>
                                 simp
                                 apply opHash_neqRight
                                 assumption
                    | Sum.inr x =>
                                 simp
                                 apply opHash_neqLeft
                                 assumption
                    -- Proof ob
                    { apply eq_true; simpa }
          | Right => simp
                     unfold LinChooser at hkC
                     have hbB
                     : ¬ headH = Knowing.inPathSeq 0 (by simp) K
                     := by simpa [ Knowing.inPathSeq ]
                     rw [ ite_cond_eq_true ] at hkC
                     simp at hkC
                     have hE := HInd (proposer.pathNode 1) lastH (Knowing.inPathSeq 1 (by simp) K)
                                      ( Proposer.DropHeadHC ℍ proposer )
                                      hkC (Knowing.DropHCKnowingSeq K)
                     rw [ <- hE ]
                     simp [ Chooser.LinPlayer.nextChooser ]
                     congr
                     simp [ Knowing.inPathSeq , Knowing.DropHCKnowingSeq]
                     rw [ Fin.foldl_succ, Fin.foldl_zero ]
                     apply funext₃
                     intro p a b
                     repeat rw [ Fin.foldl_succ ]
                     simp
                     congr

                     -- Proof ob
                     { simpa }

end WinningChooser
----------------------------------------

----------------------------------------
-- * DA Block: From a Binary Tree with information at the leaves, we compute a
-- Merkle Tree and just post hashes for the leaves and the top hash.
namespace FromBTreeToMTree

-- ** [Good] Proposers can defend its block against /all choosers/.  All
-- choosers includes /good choosers/ too. However, there is an extrinsic (meta?)
-- reasoning here. Good choosers will refrain from playing, they only play when
-- they can detect that something is wrong. In this case, something wrong is
-- when the top hash is not what it is supposed to be from /knowledge/.
--
theorem goodProposersWin
  {α ℍ : Type}[lfulEq : BEq ℍ][LawfulBEq ℍ][h : Hash α ℍ][m : HashMagma ℍ]
  -- Assumptions about hashing. But we never used them?!
  -- No, we do not need them here. We model hash functions as functions, so we
  -- only need them to be defined and returning the same value to the same
  -- input.
  --
  (knowledge : BTree α)
  --
  : forall (chooser : ChooserStrategy ℍ) (proposedH : ℍ),
  let abknowledge := @medTrees _ _ h m knowledge
  -- Assumption
  (abknowledge.getI == proposedH) ->
  --
  let da : ComputationTree ℍ := ⟨ knowledge.map h.mhash , proposedH ⟩
  let goodP : ProposerStrategy α ℍ := simpGoodGen knowledge
  treeArbitrationGame da goodP chooser = Player.Proposer
  := by
  induction knowledge with
  -- We reached a leaf.
  | leaf _v =>
    intros chooser proposed
    simp
    intro Hproposed
    simp [medTrees,ABTree.getI,ABTree.map,ABTree.getI'] at Hproposed
    simpa [treeArbitrationGame, condWProp]
  | node al ar IndL IndR =>
    intro chooser
    simp [treeArbitrationGame]
    cases chooser with
    | node cfun cl cr =>
      simp
      cases cfun
        (_ , ABTree.getI' (fun e ↦ e.2) (fun e ↦ e.1) (propTree al),
          ABTree.getI' (fun e ↦ e.2) (fun e ↦ e.1) (propTree ar)) with
        | some nextSt =>
          cases  nextSt with
          | Now =>
            simp [condWProp,medTrees,ABTree.map]
            congr
          | Continue subTree =>
            cases subTree with
            | Left =>
              simp
              have indApp := IndL cl (ABTree.getI' (fun e ↦ e.2) (fun e ↦ e.1) (propTree al))
                   (by simp [medTrees]
                       unfold ABTree.getI
                       apply getMapLaw
                   )
              assumption
            | Right =>
              simp
              have indApp := IndR cr (ABTree.getI' (fun e ↦ e.2) (fun e ↦ e.1) (propTree ar))
                   (by simp [medTrees]
                       unfold ABTree.getI
                       apply getMapLaw
                   )
              assumption
        | none => simp
    | leaf => simp


-- * [Good] Choosers win when something is wrong.
-- Something is wrong when top hash differs from what it should be.
--
-- What I am missing here is that proposer should be consistent.
-- In other words, it is something I need to check when playing the game!
--
theorem goodChoosersWin
  {α ℍ : Type}[BEq ℍ][LawfulBEq ℍ][h : Hash α ℍ][m : HashMagma ℍ]
  --
  (knowledge : BTree α)
  :
  forall (proposer : ProposerStrategy α ℍ)(topHash : ℍ),
  -- Top Hash is bad!
  (medTrees knowledge).getI != topHash ->
  --
  treeArbitrationGame ⟨ knowledge.map h.mhash , topHash⟩ proposer (simpChooser knowledge)
  = Player.Chooser
  := by
  induction knowledge with
  | leaf _v =>
    intros proposer topHash badTop
    unfold treeArbitrationGame
    simp [BTree.map ]
    cases proposer with
    | leaf kh =>
      cases kh with
      | none => simp
      | some hP =>
        simp
        simp [medTrees, propTree,ABTree.map,ABTree.getI,ABTree.getI'] at badTop
        simp [condWProp]
        intros _same
        assumption
    | node _b _ _ => simp
  | node bl br IL IR =>
    intros proposer topHash badTop
    unfold treeArbitrationGame
    simp [BTree.map]
    cases proposer with
    | leaf mpH => simp
    | node mProp proposerLeft proposerRight =>
      cases mProp with
      | none => simp
      | some props =>
        simp [simpChooser, ABTree.map, ChooserStr]
        cases propBad : m.comb props.1 props.2 != topHash with
        | true => simp [condWProp]; simp at propBad; assumption
        | false =>
            simp
            cases HCL : props.1 != ABTree.getI' (fun e ↦ e.2) (fun e ↦ e.1) (@propTree _ _ h m bl) with
            | true =>
              simp
              have indL := IL proposerLeft props.1 (by simp [medTrees,ABTree.getI]; rw [getMapLaw _ _ _ _ _]; simp; simp at HCL; intro f;apply HCL; rw [<-f])
              assumption
            | _ =>
                simp
                cases HCR : props.2 != ABTree.getI' (fun e ↦ e.2) (fun e ↦ e.1) (@propTree _ _ h m br) with
                  | true =>
                    simp
                    have indR := IR proposerRight props.2 (by simp [medTrees,ABTree.getI]; rw [getMapLaw _ _ _ _ _]; simp; simp at HCR; intro f;apply HCR; rw [<-f])
                    assumption
                  | _ => -- Impossible case!
                    simp [condWProp] at *
                    simp [medTrees,propTree,ABTree.map] at badTop
                    rw [<- HCL] at badTop
                    rw [<- HCR] at badTop
                    simp [ABTree.getI,ABTree.getI'] at badTop
                    contradiction
end FromBTreeToMTree
----------------------------------------

----------------------------------------
-- * Element is in Tree.
-- This is kinda an auxiliary lemma.
-- We want to say that an element is an element in a (tree) hash.
namespace ElemInTree

-- ** Retro compability of games
--  In our first POC, we identified good proposers as those defining two
--  sequences of hashes: spine and sibilings. Plus some properties.
--
-- Here, we show how to build a winning proposer (from previous sections) from
-- elements in tree.
-- Good thing is that we can use it for different (equivalent?) games:
-- logarithmic, linear and multi-cuts.
def proposerSkeleton
   {α ℍ : Type}{n : Nat}
   [BEq ℍ]
   [mhash : Hash α ℍ][mag : HashMagma ℍ]
   --
   (elem : α)
   (data : BTree α)
   (path : ISkeleton n.succ)
   -- Path |path| leads to element |elem| in tree |data|
   (hyp : IndexABTreeI path (@propTree _ _ mhash mag data)
        = some (.inl ⟨ elem ,  mhash.mhash elem ⟩ ))
   : have ⟨ spine, sibs ⟩ := BStrategies (fun e => e.2) (fun e => e.1) path (@propTree _ _ mhash mag data) ⟨ elem ,  mhash.mhash elem ⟩ hyp
   WinningProposer.PropHash n.succ (spine ⟨ 0 , by simp⟩ ) ( spine $ Fin.last n.succ)
   :=
    -- Strategies definitions
    ⟨ by simp , ⟨ (BStrategies (fun e => e.2) (fun e => e.1) path (@propTree _ _ mhash mag data) ⟨ elem ,  mhash.mhash elem ⟩ hyp).1  , (BStrategies (fun e => e.2) (fun e => e.1) path (@propTree _ _ mhash mag data) ⟨ elem ,  mhash.mhash elem ⟩ hyp).2⟩
     -- Props
     -- Good init
    , by simp at *
    --  Good Root
    , by simp [Fin.last]
    -- Good Mid
    , by apply allGamesStrategies
    ⟩

-- TODO Prove good proposers (from previous definitions) always win the the ElemInTree game.
-- theorem goodPropWins (gProp : WinningProposer.PropHash n.succ (spine ⟨ 0 , by simp⟩ ) ( spine $ Fin.last n.succ))
--   : forall (ch : ...) , elemInHGame _da gProp ch = Player.Proposer
--   := sorry


-- ** Good Chooser
--
-- In the case DAs are made showing elements, we also need some notion of
-- equality over elements. Here, there is no collison meta-problems.
theorem goodChoosersWinA
  {α ℍ : Type}[BEq α][LawfulBEq α][BEq ℍ][LawfulBEq ℍ][h : Hash α ℍ][m : HashMagma ℍ]
  -- + DA
  {n : Nat}
  (da : ElemInTreeN n α ℍ)
  -- + Knowledge
  (knowledge : BTree α)
  -- knowledge is correct
  (kCorrect : (@propTree _ _ h m knowledge).getHash = da.mtree)
  -- + Chooser challenge when there is something wrong.
  (hyp : IndexABTreeI da.1.2 (@propTree _ _ h m knowledge) = none
       ∨ (exists e : (α × ℍ), IndexABTreeI da.1.2 (@propTree _ _ h m knowledge) = some (.inl e)
                            ∧ e.1 != da.1.1))
  -- + Proposer
  (proposer : Sequence n (Option (PMoves ℍ)))
  :
  elemInHGame da proposer hasManyChoosers
  = Player.Chooser
  := by
   revert knowledge kCorrect hyp proposer
   induction n with
   | zero =>
     intros knowledge kCorrect hyp proposer
     have daE := ElemInTreeN0 da
     simp [elemInHGame, SingleLastStep, condWProp]
     cases hyp with
     | inl HToNone =>
        have daE := ElemInTreeN0 da
        rw [daE] at HToNone
        cases knowledge with
        | leaf v =>
          simp [propTree, IndexABTreeI] at HToNone
        | node bl br =>
          simp [propTree,IndexABTreeI] at HToNone
     | inr HToAnother =>
        have ⟨ ⟨ elem , elemHash ⟩ , ⟨ pathProof, hashProof ⟩ ⟩ := HToAnother
        simp at hashProof
        rw [daE] at pathProof
        have todoThm : forall {γ ε θ : Type} (t : ABTree (γ × ε) θ) el elh, IndexABTreeI nilSeq t = some (.inl (el, elh)) ->  t = .leaf (el, elh) := sorry
        apply todoThm at pathProof
        rw [pathProof] at kCorrect
        rw [ <- kCorrect]
        simp [ABTree.getHash,ABTree.getI']
        have someSteps : h.mhash elem = elemHash := sorry
        rw [<- someSteps]
        -- No Collision Assumptino
        have noCollisions : ¬ elem = da.data.1 -> ¬ h.mhash da.data.1 = h.mhash elem := sorry
        apply noCollisions
        assumption
   | succ pn HInd =>
     intros knowledge kCorrect hyp proposer
     simp [elemInHGame]
     split
     { case succ.h_1 _HProp => simp}
     { case succ.h_2 HPprop x proposed =>
       simp [hasManyChoosers,chooserNoData]
       cases H : da.mtree != m.comb x.1 x.2 with
       | true => simp [SingleMidStep, condWProp]; simp at H; intro FF;apply H; rw [FF]
       | false =>
         simp
         cases Side : da.data.2 0 with
         | inl _ =>
           simp
           cases knowledge with
           | leaf v =>
             -- Path proposed is longer than tree brach!
             simp at H
             simp [propTree,ABTree.getHash,ABTree.getI'] at kCorrect
             -- We have that |x1 ⊕ x2 = hash v|, our hash assumptinos should prohibit it? -- Hash Assumption
             sorry
           | node bl br =>
             -- simp [propTree] at kCorrect
             rw [getHashPropNode] at kCorrect
             simp at H
             -- hashes hashing to same hash must be the same. -- Hash Assumption
             have hashHyp : forall (h1 h2 h3 h4 : ℍ), m.comb h1 h2 = m.comb h3 h4 -> h1 = h3 := sorry
             rw [ <- kCorrect ] at H
             apply hashHyp at H
             -- have hypLeft := _
             have hypLeft : (IndexABTreeI (Fin.tail da.data.2) (@propTree _ _ h m bl) = none
                            ∨ ∃ e, IndexABTreeI (Fin.tail da.data.2) (@propTree _ _ h m bl) = some (Sum.inl e) ∧ (e.1 != da.data.1) = true)
                            := by
                             simp
                             cases hyp with
                             | inl HYP =>
                               left
                               simp [IndexABTreeI] at HYP
                               rw [Side] at HYP
                               simp at HYP
                               assumption
                             | inr HYP =>
                               right
                               have ⟨ ⟨ a , xx ⟩ , pr ⟩ := HYP
                               exists a
                               have ⟨ pTree , neq ⟩ := pr
                               simp at neq
                               apply And.intro
                               { exists xx
                                 simp [IndexABTreeI] at pTree
                                 rw [Side] at pTree
                                 simp at pTree
                                 assumption
                               }
                               { assumption }
             have hInd := HInd ⟨ ⟨ da.data.1 , Fin.tail da.data.2⟩ , x.1 ⟩ bl H hypLeft (Fin.tail proposer)
             assumption
         | inr _ => _ -- Same but on |br|
     }

theorem goodChooserWin
  {α ℍ : Type}[BEq ℍ][LawfulBEq ℍ][h : Hash α ℍ][m : HashMagma ℍ]
  -- + DA
  {n : Nat}
  (da : ElemInTreeH n ℍ) -- There is no α here!
  -- + Knowledge
  (knowledge : BTree α)
  (kCorrect : (@propTree _ _ h m knowledge).getHash = da.mtree)
  -- + Chooser challenge when there is something wrong.
  (hyp : IndexABTreeI da.1.2 (@propTree _ _ h m knowledge) = none
       ∨ (exists e : (α × ℍ), IndexABTreeI da.1.2 (@propTree _ _ h m knowledge) = some (.inl e)
                            ∧ e.2 != da.1.1))
  (proposer : Sequence n (Option (PMoves ℍ)))
  : -- Then, knowledgeless chooser strategy wins.
  elemInHGameH da
    proposer
    -- Funny thing here, choosers not require to know the
    -- original data but only to know when to challenge.
    hasManyChoosers
  = Player.Chooser
  := sorry

-- Here we need weaker assumptions?
theorem wiseChooser
  {α ℍ : Type}[BEq α][LawfulBEq α][BEq ℍ][LawfulBEq ℍ][h : Hash α ℍ][m : HashMagma ℍ]
  -- + DA
  {n : Nat}
  (da : ElemInTreeN n α ℍ)
  -- + Knowledge
  (knowledge : BTree α)
  -- knowledge is correct
  (kCorrect : (@propTree _ _ h m knowledge).getHash = da.mtree)
  -- + Chooser challenge when there is something wrong.
  (hyp : IndexABTreeI da.1.2 (@propTree _ _ h m knowledge) = none
       ∨ (exists e : (α × ℍ), IndexABTreeI da.1.2 (@propTree _ _ h m knowledge) = some (.inl e)
                            ∧ e.1 != da.1.1))
  -- + Proposer
  (proposer : Sequence n (Option (PMoves ℍ)))
  :
  elemInHGame da proposer (chooserData (@propTree _ _ h m knowledge) da)
  = Player.Chooser
  := by revert knowledge proposer da
        induction n with
        | zero =>
          intros da knowledge kCorrect hyp proposer
          sorry
        | succ pn HInd =>
          intros da knowledge kCorrect hyp proposer
          simp [elemInHGame]
          split
          { case succ.h_1 HPProp => simp }
          { case succ.h_2 HEQ proposed move =>
            cases knowledge with
            | leaf v =>
              simp [propTree]
              simp [chooserData, SingleMidStep, condWProp]
              simp [propTree, ABTree.getHash, ABTree.getI'] at kCorrect
              -- Same as before
              sorry -- h1 ⊕ h2 != hash(v)
            | node bl br =>
              simp [propTree,chooserData]
              -- Some cases here.
              cases HL : proposed.1 != (propTree bl).getHash with
              | true =>
                simp; simp [SingleMidStep,condWProp]; simp at HL
                rw [getHashPropNode] at kCorrect
                rw [<- kCorrect]
                -- One of the laws of hash
                -- a != b => comb a c != comb b c
                sorry
              | false =>
                cases HR : proposed.2 != (propTree br).getHash with
                | true => sorry -- same as before
                | false =>
                  simp
                  -- inductive hipothesis.
                  sorry
            }

end ElemInTree
----------------------------------------
