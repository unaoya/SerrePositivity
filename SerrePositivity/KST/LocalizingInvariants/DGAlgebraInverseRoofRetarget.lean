module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraInverseRoofRefinement

/-!
概要：元の一切断逆 roof の対象段を低い段へ移し、元の左右三角形を保持する。
方針：分子を源塔の遷移で後合成し、右経路は標的塔の同じ遷移で後合成する。
規約：分母・頂点・左細分を取り替えない。使われ方：class 整合の低い対象段への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.NonpositiveInverseRoof
open ProExcision
variable (R : Type u) [CommRing R] {X Y : Tower (Mon (Complex R))} {f : LevelHom X Y}
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R f i m hi) {j : ℕ} (hj : j ≤ i)

def retargetRightPath : Path.Witness R ((c.roof.numerator ≫ X.transition hj) ≫ f.app j)
    (c.roof.denominator ≫ Y.transition (hj.trans hi)) where
  hom := c.rightPath.hom ≫ Path.map R (Y.transition hj)
  source_eq := by
    rw [Category.assoc, Path.map_source, ← Category.assoc, c.rightPath.source_eq,
      Category.assoc, ← f.naturality hj, ← Category.assoc]
  target_eq := by
    rw [Category.assoc, Path.map_target, ← Category.assoc, c.rightPath.target_eq,
      Category.assoc, Y.transition_comp hi hj]

/-- 元の実データを保つ、対象段だけの移送。 -/
def retarget : NonpositiveInverseRoof R f j m (hj.trans hi) where
  roof := c.roof.postcompose R (X.transition hj)
  roof_nonpositive := c.roof_nonpositive
  source := c.source
  source_nonpositive := c.source_nonpositive
  sourceProjection := c.sourceProjection
  sourceProjection_epi := c.sourceProjection_epi
  sourceProjection_quasiIso := c.sourceProjection_quasiIso
  sourceLift := c.sourceLift
  source_denominator := c.source_denominator
  source_numerator := by
    change c.sourceLift ≫ (c.roof.numerator ≫ X.transition hj) = _
    rw [← Category.assoc, c.source_numerator, Category.assoc, X.transition_comp hi hj]
  rightPath := retargetRightPath R c hj

lemma retarget_denominator : (retarget R c hj).roof.denominator = c.roof.denominator := rfl

lemma retarget_numerator : (retarget R c hj).roof.numerator =
    c.roof.numerator ≫ X.transition hj := rfl

lemma retarget_rightPath : (retarget R c hj).rightPath.hom =
    c.rightPath.hom ≫ Path.map R (Y.transition hj) := rfl

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.NonpositiveInverseRoof
