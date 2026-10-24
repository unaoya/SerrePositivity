module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNativeRightRoofSource
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoNonpositiveDiagonal

/-!
概要：元の二切断右逆の左欠損を、指定全経路を持つ非正次数対角模型への射に束ねる。
方針：元の二射と f の先の実経路を cospan lift に渡し、cover へ一意に持ち上げる。
規約：欠損経路を定数経路に取り替えない。使われ方：対角右逆による左経路の反映。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision HomotopyPullbackModel
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)}
  (f : LevelHom A B) {m k : ℕ} {hmk : m ≤ k}
  (c : NativeRightInverseRoof R (f.map (postnikovFunctor R 2)) m k hmk)

local instance defectSource_nonpositive : (c.nonpositiveSource R).X.IsStrictlyLE 0 :=
  coverComplex_nonpositive R (cellResolution R (postnikov R (A.obj k).obj 2))

local instance defectOriginalSource_nonpositive :
    ((A.map (postnikovFunctor R 2)).obj k).X.IsStrictlyLE 0 :=
  postnikov_nonpositive R (A.obj k).obj 2

def postnikovTwoDefectPair : c.nonpositiveSource R ⟶
    ((postnikovTwoDiagonalTarget R f).obj m).obj :=
  connectiveCoverLift R (lift R (postnikovMap R (f.app m).hom 2)
    (postnikovMap R (f.app m).hom 2) (c.sourceLift R ≫ c.roof.numerator)
    (c.sourceProjection R ≫ postnikovMap R (A.transition hmk).hom 2)
    (c.sourceDefectAfterF R))

lemma postnikovTwoDefectPair_left : postnikovTwoDefectPair R f c ≫
    postnikovTwoDiagonalLeft R f m = c.sourceLift R ≫ c.roof.numerator := by
  rw [postnikovTwoDefectPair, postnikovTwoDiagonalLeft, ← Category.assoc,
    connectiveCoverLift_inclusion, lift_left]

lemma postnikovTwoDefectPair_right : postnikovTwoDefectPair R f c ≫
    postnikovTwoDiagonalRight R f m =
      c.sourceProjection R ≫ postnikovMap R (A.transition hmk).hom 2 := by
  rw [postnikovTwoDefectPair, postnikovTwoDiagonalRight, ← Category.assoc,
    connectiveCoverLift_inclusion, lift_right]

lemma postnikovTwoDefectPair_path : postnikovTwoDefectPair R f c ≫
    connectiveCoverInclusion R ((postnikovTwoDiagonalRawTarget R f).obj m) ≫
      path R (postnikovMap R (f.app m).hom 2) (postnikovMap R (f.app m).hom 2) =
    (c.sourceDefectAfterF R).hom := by
  rw [postnikovTwoDefectPair, ← Category.assoc, connectiveCoverLift_inclusion, lift_path]

variable {i : ℕ} (him : i ≤ m)

lemma postnikovTwoDiagonalLeft_naturality :
    ((postnikovTwoDiagonalTarget R f).transition him).hom ≫ postnikovTwoDiagonalLeft R f i =
      postnikovTwoDiagonalLeft R f m ≫ postnikovMap R (A.transition him).hom 2 :=
  ((coverTowerCounit R (postnikovTwoDiagonalRawTarget R f)).comp
    (leftProjection R (f.map (postnikovFunctor R 2))
      (f.map (postnikovFunctor R 2)))).naturality him

lemma postnikovTwoDiagonalRight_naturality :
    ((postnikovTwoDiagonalTarget R f).transition him).hom ≫ postnikovTwoDiagonalRight R f i =
      postnikovTwoDiagonalRight R f m ≫ postnikovMap R (A.transition him).hom 2 :=
  ((coverTowerCounit R (postnikovTwoDiagonalRawTarget R f)).comp
    (rightProjection R (f.map (postnikovFunctor R 2))
      (f.map (postnikovFunctor R 2)))).naturality him

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
