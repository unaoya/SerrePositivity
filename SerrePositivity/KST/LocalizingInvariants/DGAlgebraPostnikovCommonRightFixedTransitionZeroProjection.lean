module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightFixedTransitionRefinement
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessMapOver

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightFixedTransitionZeroProjection
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：fixed Γ の遷移の右像を、零底に相対的な元の G として保持する。
方針：底変更射による相対経路の移送と、全経路の厳密同定を使う。
規約：Γ の元の射影と指定端点を保持。使われ方：右 class 互換性の実比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} (hj : j ≤ i)

def postnikovCommonRightGlueZeroRelative :=
  PostnikovCommonCore.postnikovCommonRightGlueZeroRelative
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

variable (e : PostnikovZeroLayerInverse R 1 f j i hj)

lemma postnikovCommonClassFixedTransitionZeroRight_projection :
    (postnikovCommonClassFixedTransitionZeroRightPath R f c d hj e).hom ≫
      Path.map R (SquareZero.projection _ _) =
    (postnikovCommonClassStandardGlueProjection R f c d ≫
      postnikovCommonRightClassifyingBase R f c d hj) ≫
      Path.diagonal R (postnikov R (B.obj j).obj 0) :=
  PostnikovCommonCore.postnikovCommonClassFixedTransitionZeroRight_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

/-- 同じ G の端点表示で、全射は fixed 遷移の元の右像そのもの。 -/
def postnikovCommonRightFixedTransitionZeroRelative :=
  PostnikovCommonCore.postnikovCommonRightFixedTransitionZeroRelative
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
