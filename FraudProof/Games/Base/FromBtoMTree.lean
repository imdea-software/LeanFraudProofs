-- import FraudProof.DAssertions
import FraudProof.Games.GameDef -- Players, Winner
import FraudProof.Players

import FraudProof.DataStructures.BTree -- Btree
import FraudProof.DataStructures.MTree -- MTree
import FraudProof.DataStructures.Hash -- hash classes

import FraudProof.Extras.BToMTree -- Indexing MMTrees

----------------------------------------
-- * Simply structure.
-- This one is assuming that |α| is known. We can do a little bit better.
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

----------------------------------------
-- * BTree as hashes.
-- We know the structure of the data plus the hashes of their leaves.
structure ComputationTree (ℍ : Type) where
  computation : BTree ℍ -- Btree in this case, in can be generalized
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
  | .leaf h =>
    match reveler pos with
    -- Only accepted move here is |End|.
    | some (.End v) =>
      condWProp $ o.mhash v == h
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

-- Indexed Traversing data.
-- Last guard shows we still do not have enough data connecting
-- previous options with current state.
def compI {α ℍ : Type}
    [BEq ℍ][o : Hash α ℍ][m : HashMagma ℍ]
    (pos : Skeleton)
    (da : ComputationTree ℍ)
    --
    (reveler : Skeleton -> Option (PMoves' α (ℍ × ℍ)))
    (chooser : Skeleton -> (ℍ × ℍ) -> Option ChooserMoves)
    --
    : Winner := match _HC : IndexBTree pos da.computation , reveler pos with
    | some (.inl h), some (.End v)  =>
      condWProp $ o.mhash v == h
    | some (.inr ⟨ cl , cr ⟩) , some (.Next proposed) =>
      match chooser pos proposed with
      | some (.Now) =>
        condWProp $ m.comb proposed.1 proposed.2 == da.res
      | some (.Continue .Left) =>
        compI (pos ++ [ .inl () ]) ⟨ cl , proposed.1 ⟩ reveler chooser
      | some (.Continue .Right) =>
        compI (pos ++ [ .inr () ]) ⟨ cr , proposed.2 ⟩ reveler chooser
      -- No moves
      | _ => Player.Proposer
    -- Invalid moves from Proposer.
    -- I don't think this guard is reachable?
    | _ , _ => Player.Chooser
termination_by da.computation
decreasing_by
  all_goals simp_wf
  { have thS := (sizeIBTree pos da.computation cl cr _HC).1; assumption}
  { have thS := (sizeIBTree pos da.computation cl cr _HC).2; assumption}


def arbInit {α ℍ : Type}
    [BEq ℍ][Hash α ℍ][HashMagma ℍ]
    (da : ComputationTree ℍ)
    --
    (reveler : Skeleton -> Option (PMoves' α (ℍ × ℍ)))
    (chooser : Skeleton -> (ℍ × ℍ) -> Option ChooserMoves)
    --
    : Winner := compTreeArbitration .nil da reveler chooser

----------------------------------------
-- * Index Trees (overcomplicated)
-- Same as before, but with enriched trees with
-- + pre-computed hashes (assumed correct?) <- removed this, we may not need them
-- (add it to the next game)
-- + shortest path : for indexing trees (positions)
-- + longest path provide full strategies
structure DAIxTrees (ℍ: Type) (s l : Nat) where
  computationTree : LeafITree ℍ s l -- Tree with Hashes as leaves
  merkleTree : ℍ -- res


-- We can define complete games. Players play until the end.
-- We can easily adapt it to players abandoning the game, but we have the
-- machinery to specify the game completely.
-- def sizedArbitrage {α ℍ : Type}[BEq ℍ][o : Hash α ℍ][m : HashMagma ℍ]
--     {s l curr : Nat}
--     (currRange : curr < s )
--     (da : DAIxTrees ℍ s l)
--     (pos : ISkeleton curr)
--     --
--     -- Players strategies should be define at all possible
--     -- board states.
--     (proposer : MMTree α ℍ s l)
--     (chooser : MMTree Unit (ℍ × ℍ -> ChooserMoves) s l)
--     --
--     : Winner :=
--     match IdxMMTreeI _ da.computationTree pos , IdxMMTreeI currRange proposer pos with
--     -- Good Moves
--     -- Path leads to a leaf
--     | .inl ⟨ h , _ ⟩ , .inl ⟨ v , _ ⟩ =>
--        condWProp $ o.mhash v == h
--     -- Path leads to a node
--     | .inr ⟨ _ , bl , br ⟩ , .inr ⟨ _ , hl , hr ⟩ =>
--        match IdxMMTreeI currRange chooser pos with
--        | .inl _ => Player.Proposer -- wrong move
--        | .inr ⟨ f , _ , _ ⟩ =>
--          match f ⟨ hl , hr ⟩ with
--          | .Now =>
--           condWProp $ m.comb hl hr == da.merkleTree
--          | .Continue .Left =>
--            sizedArbitrage _ ⟨ _ , hl ⟩ (Fin.snoc pos (.inl ())) _ _
--          | .Continue .Right => _
--     -- Bath Moves
--     | .inl _ , .inr _ => Player.Chooser -- Wrong move
--     | .inr _ , .inl _ => Player.Chooser -- Wrong move

----------------------------------------
-- * MAP and stuff players.
--

def mapArbitrationGame _
----------------------------------------
