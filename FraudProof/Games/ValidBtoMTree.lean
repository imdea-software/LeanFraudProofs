import FraudProof.DAssertions
import FraudProof.Games.GameDef -- Players, Winner
import FraudProof.Players

import FraudProof.Games.ElemInTree -- Block hash consitency

-- Property needed to verify this:
-- A block is |vf : α -> Bool|-valid if all elements are valid.
-- DA : ⟨ data , mTree ⟩ is vf-valid ↔ data.elems.all vf
-- equivalent (do we need classic logic here?)
-- DA : ⟨ data , mTree ⟩ is *not* vf-valid ↔ ∃ (v : α), v ∈ data.elems ∧ ¬ (vf v)

def arbValid {α ℍ : Type}
    (vFunc : α -> Bool)
    [BEq ℍ]
    [Hash α ℍ][HashMagma ℍ]
    --
    (da : ElemInMTree α ℍ)
    --
    (proposer : Skeleton -> ProposerMoves ℍ)
    (chooser : Skeleton -> ProposerMoves ℍ -> ChooserSmp)
    : Winner
    := if vFunc da.elem -- This is run by a trusted source.
    then Player.Proposer -- Insta win Proposer
    else arbElem .nil da proposer chooser
