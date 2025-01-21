import FraudProof.Games.GameDef -- Players, Winner

def Range (α : Type) := α × α

@[simp]
def all_true (ls : List Bool) : Bool := ls.all id

def leaf_condition_range {ℍ : Type}[BEq ℍ]
  := fun (_k : Unit) (h : ℍ) (hda : ℍ × ℍ)
     => condWProp $ all_true
     [ h == hda.1 , hda.1 == hda.2]

-- Defining mid condition when going forward one step.
-- That means
-- [a -> b]!n.succ ->
--  P-> (c,d), [a -> c]!n and (c (+) d = b)
def mid_condition_range_one_step_forward {ℍ : Type}[BEq ℍ][HashMagma ℍ]
  : Unit -- Arena conditions
  -> SkElem -- Extra proposed
  -> Range ℍ -- Current Data
  -- Data Proposed
  -> Range ℍ -> Range ℍ
  -> Winner
  := (fun _ side hres hl hr =>
        let ⟨ parent_from , parent_to⟩ := hres -- [a -> b]
        let ⟨ left_from , left_to⟩ := hl -- [a -> c]
        let ⟨ right_l , right_r ⟩ := hr -- (c, d)
        let new_to := match side with
                      | .inl _ => right_l
                      | .inr _ => right_r
          -- Mid condition is the expected one
        condWProp $
          all_true
          [ parent_from == left_from
          , left_to == new_to
          , op_side side right_l right_r == parent_to
          ]
      )
