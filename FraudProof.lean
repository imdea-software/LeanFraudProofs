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
  {α ℍ : Type}[BEq ℍ][h : Hash α ℍ][m : HashMagma ℍ]
  -- Assumptions about hashing
  [CollResistant α ℍ] -- No two elemts share hashes
  [SLawFulHash ℍ] -- Combining diff hashes returns diff hashes.
  --
  (knowledge : BTree α)
  --
  : forall (chooser : ChooserStrategy ℍ),
  have abknowledge := @medTrees _ _ h m knowledge
  have da : ComputationTree ℍ := ⟨ knowledge.map h.mhash , abknowledge.getI ⟩
  have goodP : ProposerStrategy α ℍ := simpGoodGen knowledge
  treeArbitrationGame da goodP chooser = Player.Proposer
  := sorry

-- * [Good] Choosers win when something is wrong.
-- Something is wrong when top hash differs from what it should be.
--
theorem goodChoosersWin
  {α ℍ : Type}[BEq ℍ][h : Hash α ℍ][m : HashMagma ℍ]
  -- Assumptions about hashing
  [CollResistant α ℍ] -- No two elemts share hashes
  [SLawFulHash ℍ] -- Combining diff hashes returns diff hashes.
  --
  (knowledge : BTree α)
  (top : ℍ)
  :
  have abknowledge := @medTrees _ _ h m knowledge
  have da : ComputationTree ℍ := ⟨ knowledge.map h.mhash , top ⟩
  -- Hash |top| does not matches our knowledge
  abknowledge.getI != top
  --
  -> forall (proposer : ProposerStrategy α ℍ),
     treeArbitrationGame da proposer (simpChooser knowledge)
     = Player.Chooser
  := sorry
end FromBTreeToMTree
----------------------------------------
