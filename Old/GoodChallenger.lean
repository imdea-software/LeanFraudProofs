import FraudProof
----------------------------------------
-- * A GoodChallenger

def treeTohashPath ( p : TreePath Value ) : Path :=
  List.map (Sum.map (MTree.hash ∘ hash_BTree) (MTree.hash ∘ hash_BTree))  p

def sumP {α : Type} ( e : Sum α α ) : α := (Sum.elim id id) e

-- This is a scan computation. I'll write it down first and then Lean it.
def PathComputation ( v : Hash ) ( path : Path ) : List Hash
:= match path with
   | List.nil => List.nil
   | List.cons pS ps =>
     let nodeHash := opHash v pS
     nodeHash :: ( PathComputation nodeHash ps )

-- PathComputation v p = List.drop 1 (ScanPath v p)
def ScanPath ( v : Hash ) ( path : Path ) : List Hash
:= List.scanl opHash v path

-- Since we play games in a range | 0 ... init.pL - 1|, we only need to
-- provide an strategy on such range.
-- This is equivalent to play finite games. Very finite, as soon as we start
-- the game, we have a cap to the number of moves.
def CGoodPlayer
  (v : Value) (path : TreePath Value)
  : ChallengerReq
  :=
    let hashPath := treeTohashPath path
    -- I don't know if the top hash is needed.
    let pathHash := List.reverse $ List.drop 1 $ ScanPath (H v) hashPath
  -- Good Challenger knows that | valH = H val |
  { init := { pL := List.length path
            , val := v
            , valH := H v }
  , strategy := fun p
             => List.get pathHash { val := p.val
                                  , isLt := by
                                    { have LenEq : pathHash.length = path.length := by
                                      { rw [ List.length_reverse ]
                                        simp
                                        rw [ ScanPath , List.length_scanl]
                                        simp
                                        exact List.length_map _ _
                                      }
                                      rw [ LenEq ]
                                      simp
                                    }}
  , sibling := fun p => List.get (List.reverse hashPath)
                                 { val := p.val
                                 , isLt := by { have LenEq : List.length (List.reverse hashPath) = List.length path :=
                                                     by { rw [ List.length_reverse ]
                                                          exact List.length_map path _ }
                                                rw [ LenEq ]
                                                simp
                                              } }
  }

theorem GoodCWinsOneStep:
  ( v : Value )
  ( path : TreePath Value )




theorem GoodChallengerAlwaysWin
  -- Given a trii
  ( bt : MTree )
  ( v : Value )
  ( D : Challenged )
  ( path : TreePath Value )
  ( vInbt : containCompute v (treeTohashPath path) bt )
  : MembershipGame (CGoodPlayer v path) D  bt.hash = Winner.Challenger
:= by {
  induction path with
  | nil =>
    rw [ MembershipGame , CGoodPlayer ]
    simp
    rw [ treeTohashPath , containCompute] at vInbt
    simp at vInbt
    rw [ nodeIn ] at vInbt
    rw [ listPathHashes ] at vInbt
    rw [ MTree.hash ]
    cases HBt : bt with
    | node h => rw [ HBt ] at vInbt; simp at *; exact vInbt
  | cons p ps HInd => _
}
