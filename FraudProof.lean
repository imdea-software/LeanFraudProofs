-- This module serves as the root of the `FraudProof` library.
-- Import modules here that should be built as part of the library.

-- Data Structures
import FraudProof.DataStructures.Value
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


import Batteries.Data.Fin.Lemmas

namespace LinearGame
-- * Good Proposer winss Linear Game

open Proposer
open WinningProposer
open BotUpLin

-- ** /Good
theorem GChalWinsHtoLHashes (gameLength : Nat) :
    forall
    (headH lastH : Hash)
    (proposer : PropHash gameLength headH lastH)
    (chooser : Chooser.Player),
    InitHashPathGameHeadToLast gameLength proposer.pathLenNZ headH lastH proposer.strategies chooser = Winner.Proposer
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
      | zero => simp; exact GCLemmas.GChalOneH _
      | succ n =>
        simp
        cases D.strategy hv (A.strategies.pathNode ⟨ (n + 1), _ ⟩) hr with
        | Left =>
          simp
          unfold InitHashPathGameHeadToLast at HN
          have HI := HN hv ((A.strategies.pathNode ⟨n + 1, by simp⟩)) (GCShifts.DropLast _ hv hr A) D
          unfold GCShifts.DropLast at HI
          simp at HI
          have eqDropNode := DropLastNodeEq A.strategies
          have eqDropSib := DropLastSibEq A.strategies
          have eqInj := HashPathFunInj (by simp) (n + 1) (by simp) (by simp) (DropLastHC A.strategies) A.strategies ( by rw [Fin.forall_iff]; exact eqDropNode ) ( by rw [Fin.forall_iff] ; exact eqDropSib ) D hv (A.strategies.pathNode ⟨ n+1 , by simp ⟩ )
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

theorem GChalWinsHtoL (gameLength : Nat)
      (v : Value) (mt : MTree)
      (proposer : WinningProposer.WinningProp gameLength v mt)
      (chooser : Chooser.Player)
      : InitHashPathGameHeadToLast gameLength proposer.pathLenNZ (H v) mt.hash proposer.strategies chooser = Winner.Proposer
      := GChalWinsHtoLHashes gameLength (H v) mt.hash proposer chooser

  -- We cannot recover witnesses, because Lean has proof irrelevance hardcoded.
  -- theorem KWinsHtoL ( v : Value ) ( tree : BTree Value ) (vInTree : valueIn v tree)
  --   : let ⟨ path , pPath ⟩ := valueInToProof v tree vInTree
  --   exists (proposer : WinningProposer.WinningProp path.length v _),
  --     _Game = Winner.Proposer

theorem WinningProposer
    ( v : Value ) ( btree : BTree Value )
    (path : TreePath Value) (pathNNil : 0 < path.length)
    ( vInBTree : valueInProof v btree = some path)
: forall (chooser : Chooser.Player),
  have winprop := Build.WProposerCreate v btree path pathNNil vInBTree
  InitHashPathGameHeadToLast path.length pathNNil (H v) (hash_BTree btree).hash winprop.strategies chooser = Winner.Proposer
:=  by
  intros ch wp
  exact GChalWinsHtoL path.length v _ _ _


end LinearGame


namespace LogGame
-- * Good Proposer wins Logarithmic Game

open Proposer
open WinningProposer

-- Predicate to do induction over.
@[simp]
def LogWinningProp' (gL : Nat) : Prop :=
    forall
    (headH lastH : Hash)
    (proposer : PropHash gL headH lastH)
    (chooser : Chooser.Player),
    MembershipGame_2STG gL
    proposer.strategies chooser
    proposer.pathLenNZ -- path is not Zero
    headH lastH = Winner.Proposer

theorem PropHashWins (gL : Nat) : LogWinningProp' gL
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

-- One of the properties making /good/ proposers does no hold.
--
def notZero (gl : Nat) (P : HC gl)(hZ : Hash) : Prop := P.pathNode ⟨ 0 , by simp ⟩ != hZ
def notRoot (gl : Nat) (P : HC gl)(hR : Hash) : Prop := P.pathNode ⟨ gl , by simp ⟩ != hR
def notAllGames (gl : Nat)(P : HC gl) : Prop :=
  exists (p : Nat)(pRange : p < gl),
    P.pathNode ⟨ p + 1 ,  by simp; assumption ⟩ != opHash (P.pathNode ⟨ p , by omega ⟩ ) (P.pathSib ⟨ p , pRange ⟩)

-- Losing proposer is a /bad/ proposer.
-- Bad Proposers fails on (at least) one of the following props:
-- + notZero, initial hash is not correct.
-- + notRoot, final hash is not correct.
-- + there is one hash along the way that does not match up: exists p, node[p+1] = node[p] ⊕ sib[p]
--
def BadProposer { gl : Nat } (P : HC gl) ( hb ht : Hash ) : Prop
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
--   : BotUpLin.InitHashPathGameLastToHead gameLength gNZ hinit hroot P C = Winner.Chooser
--   -> notZero gameLength P hinit
--   ∨ notRoot gameLength P hroot
--   ∨ notAllGames gameLength P

end LosingProposer

namespace WinningChooser

-- If Proposer is /not good/ then, a /knowing chooser/ can wins.
-- The intuition of what a /not good/ proposer can be is 'developed' in the
-- previous namespace.

open BotUpLin

-- The following theorem is to prove that
-- If we know a path of length |gameLength| from |hbot| to |lastH|, |know :Knowing.PathProof gameLength hbot lastH|,
-- we can build a chooser to play the game, if the proposer proposed a wrong initial hash |headH|.

theorem ChooserGLHeadWrong (gameLength : Nat) (glNZ : 0 < gameLength) :
    forall
    (headH lastH : Hash)
    (hbot : Hash )
    (proposer : Proposer.HC gameLength)
    -- Game Invariant
    -- Hashes were proposed by |proposer|
    -- (gmInvHead : proposer.pathNode ⟨ 0 , by simp ⟩ = headH)
    -- (gmInvLast : proposer.pathNode ⟨ gameLength , by simp ⟩ = lastH)
    --
    (hNEQ : headH != hbot ) -- It is used! Shall I say something to the dev team?
    -- proposer is not good
    -- (badH : LosingProposer.notAllGames gameLength proposer)
    -- We need to know pathproof.
    (know : Knowing.PathProof gameLength hbot lastH)
    ,
    HashPathDrop gameLength glNZ proposer (KnowingLinChooser gameLength hbot lastH know) headH lastH
    = Winner.Chooser
    := by
    induction gameLength with
    | zero => simp at glNZ
    | succ pn HInd =>
      intros hbBad ht hb P badP k
      unfold HashPathDrop
      cases pn with
      | zero => simp; have gP := k.goodPath; simp at *; -- have pWit := k.pathWit;
                rw [ Fin.foldl_succ , Fin.foldl_zero ] at gP;
                rw [ <- gP ]
                apply opHash_neq
                assumption
      | succ ppn =>
        simp [KnowingLinChooser] at *
        cases hKC :  LinChooser (Knowing.inPathProof 0 _ k) (Knowing.inPathProof 1 _ k) hbBad (P.pathNode 1) with
        | Left => simp; simp [LinChooser] at hKC;
                  have hbB
                    : ¬ hbBad = Knowing.inPathProof 0 (by simp) k
                    := by simpa [ Knowing.inPathProof ]
                  rw [ ite_cond_eq_false ] at hKC
                  simp at hKC
                  unfold Knowing.inPathProof at hKC; rw [ Fin.foldl_succ , Fin.foldl_zero ] at hKC
                  rw [ hKC ]
                  apply opHash_neq
                  assumption

                  -- Proof obligations
                  {exact eq_false hbB}

        | Right =>
                simp
                unfold LinChooser at hKC
                have hbB -- |hb| is |Knowing.inPathProof 0 (by simp) k|
                     : ¬ hbBad = Knowing.inPathProof 0 (by simp) k
                     := by simpa [ Knowing.inPathProof ]
                rw [ ite_cond_eq_true ] at hKC
                simp at hKC
                have hE := HInd (P.pathNode 1) ht (Knowing.inPathProof 1 (by simp) k)
                                ( Proposer.DropHeadHC P )
                                -- ( by simp [ Proposer.DropHeadHC ] )
                                -- ( by simp [Proposer.DropHeadHC]; assumption )
                                hKC (Knowing.DropHCKnowing k)
                rw [ <- hE ]
                simp [ Chooser.LinPlayer.nextChooser ]
                congr
                simp [ Knowing.inPathProof, Knowing.DropHCKnowing ]
                rw [ Fin.foldl_succ , Fin.foldl_zero ]
                clear HInd badP hbB hKC -- Removing stuff to see the goal
                apply funext₃
                intro p a b
                repeat rw [ Fin.foldl_succ  (fun acc i ↦ opHash acc (k.pathWit ⟨↑i, (by omega)⟩)) hb ]
                rfl
                -- Proof obligations
                { simpa }
end WinningChooser
