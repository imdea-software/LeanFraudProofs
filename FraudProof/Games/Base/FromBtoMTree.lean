-- import FraudProof.DAssertions
import FraudProof.Games.GameDef -- Players, Winner
import FraudProof.Players

import FraudProof.DataStructures.BTree -- Btree
import FraudProof.DataStructures.MTree -- MTree
import FraudProof.DataStructures.Hash -- hash classes

-- Simply structuere
structure FromBtoMTree (α ℍ: Type) where
  data : BTree α
  merkleTree : ℍ
  -- Hash α ℍ and HashMagma ℍ
  -- Implicit assumption: this.merkleTree = MTree.hash $ hash_BTree this.data
  -- This is missing BEq ℍ to /test/ equality.


-- We assume the DA |da| was proposed by the proposer.
-- If it is right, the proposer wins.
-- If it is wrong, the chooser wins.
--
-- Each call function call here is a contract invokation.
def arbitrage
    {α ℍ : Type}
    [BEq ℍ]
    [o : Hash α ℍ][m : HashMagma ℍ]
    (pos : Skeleton)
    --
    (da : FromBtoMTree α ℍ)
    -- Naive way to implement it. Sequencial moves,
    -- the |chooser| sees what the |proposer| proposes, and then (in the next
    -- step) the |proposer| seer what the |chooser| chosed through the |pos|.
    (proposer : Skeleton -> Option (PMoves ℍ))
    (chooser : Skeleton -> PMoves ℍ -> Option ChooserMoves)
    -- Think a bit more about this one.
    : Winner
    :=
    match _h : da.data with
    -- End of the game!
    | .leaf v =>
      condWProp $ o.mhash v == da.merkleTree
    -- Moves are required
    | .node bl br =>
      -- Proposer moves
      match proposer pos with
      | none => Player.Chooser
      | some proposed =>
        -- Chooser moves
        match chooser pos proposed with
        | none => Player.Proposer -- Added later hehe
        -- Chooser challenges proposed hashes
        | some .Now => condWProp $ hProposed proposed == da.merkleTree
        -- Chooser continues the game choosing one branch
        | some (.Continue s) =>
            -- Next step is super similar
            match s with
            | .Left =>
            arbitrage
                (pos ++ [ Sum.inl () ]) -- Next position
                ⟨ bl , proposed.left ⟩ -- Next DA to check.
                proposer chooser -- Players don not change
            | .Right =>
            arbitrage
                (pos ++ [ Sum.inr () ]) ⟨ br , proposed.right ⟩
                proposer chooser -- Players don not change
    termination_by sizeOf da.data
    decreasing_by
      all_goals { simp_wf; rw [_h]; simp; try omega}

def arbitrationInit {α ℍ : Type} [BEq ℍ] [Hash α ℍ][HashMagma ℍ]
    (da : FromBtoMTree α ℍ)
    (proposer : Skeleton -> Option (PMoves ℍ))
    (chooser : Skeleton -> PMoves ℍ -> Option ChooserMoves)
    : Winner
    := arbitrage .nil da proposer chooser

-- This is not enough.
structure ComputationTree (ℍ : Type) where
  computation : BTree Unit -- Btree in this case, in can be generalized
  res : ℍ
  -- {𝔸}, fold 𝔸_hash computation = res
  -- one binary operation and leafs (In this case, that's why BTree)

def compTreeArbitration {α ℍ : Type}
    [BEq ℍ][o : Hash α ℍ][m : HashMagma ℍ]
    (pos : Skeleton)
    (da : ComputationTree ℍ)
    --
    (reveler : Skeleton -> Option (PMoves' α (ℍ × ℍ)))
    (chooser : Skeleton -> (ℍ × ℍ) -> Option ChooserMoves)
    --
    : Winner :=
  match _R : da.computation with
  -- End of the game.
  | .leaf _ =>
    match reveler pos with
    -- Only accepted move here is |End|.
    | some (.End v) =>
      condWProp $ o.mhash v == da.res
    -- Here we have, no moves or more moves.
    | _ => Player.Chooser -- wins
  -- Playing.
  | .node cl cr =>
    match reveler pos with
    -- Only accepted move here is |Next|
    | some (.Next proposed) =>
      match chooser pos proposed with
      -- Hashes proposed do not compute top hash.
      | some (.Now) => condWProp $ m.comb proposed.1 proposed.2 == da.res
      -- Chooser accpets hash and continues the game.
      | some (.Continue s) =>
        match s with
        | .Left => compTreeArbitration (pos ++ [.inl ()]) ⟨ cl , proposed.1 ⟩ reveler chooser
        | .Right => compTreeArbitration (pos ++ [.inr ()]) ⟨ cr , proposed.2 ⟩ reveler chooser
      | none => Player.Proposer
    --
    | _ => Player.Chooser
 termination_by da.computation
 decreasing_by all_goals {simp_wf; rw [_R]; simp ; try omega}

----------------------------------------
-- * Index Trees (overcomplicated)
-- Same as before, but with enriched trees with
-- + pre-computed hashes (assumed correct?) <- removed this, we may not need them
-- (add it to the next game)
-- + shortest path
-- structure DAIxTrees (α ℍ: Type) (n : Nat) where
--   data : ITree α n
--   merkleTree : ℍ

-- To implement something like this I need more information over the tree.
-- Like shortest and longest path lengths.
-- + shortest to index trees
-- + longest to ask for stategies.: ∀ (longest : Nat), (i : Fin longest -> ISkeleton i -> ProposerMoves )
-- def sizedArbitrage {α ℍ : Type}[BEq ℍ][o : Hash α ℍ][m : HashMagma ℍ]
--     {p q : Nat} -- size
--     (pLTq : p ≤ q)
--     (pos : ISkeleton p)
--     (da : DAIxTrees α ℍ q)
--     --
--     (proposer : ISkeleton p -> ProposerMoves ℍ)
--     (nextProposer : _)

    --
