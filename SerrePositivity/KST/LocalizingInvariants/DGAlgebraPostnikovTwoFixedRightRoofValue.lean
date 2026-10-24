module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedUpperRightRoofPath

/-!
概要：実右三角形のために細分した roof と、元の fixed 候補の値を比較する。
方針：実 cell 細分・準同型逆・元の上下段比較を全て保持して合成の評価則を適用する。
規約：旧非 fixed 候補との一致は主張しない。使われ方：実 roof の選択と元の値の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)
  {D : Type v} [Category.{w} D] (L : Mon (Complex R) ⥤ D) (hL : InvertsQuasiIsos R L)

lemma nonpositiveFixedRightRoof_value_eq_fixedCandidate :
    SurjectiveRoof.value R L hL (d.nonpositiveFixedRightRoof R) =
    SurjectiveRoof.value R L hL (d.fixedCandidateRoof R) := by
  simp only [nonpositiveFixedRightRoof, fixedCandidateRoof,
    SurjectiveRoof.nonpositiveNormalization_value, upperFixedRightRoof,
    SurjectiveRoof.cellRefinement_value, upperFixedRightRawRoof,
    RoofConjugation.roof, RoofConjugation.firstRoof, RoofConjugation.inverseRoof,
    rightSourceClassRoof, classModelFixedRightRoof, rawFixedCandidateRoof,
    sourceUpperRoof, targetUpperRoof, SurjectiveRoof.comp_value,
    SurjectiveRoof.ofHom_value, Category.assoc]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
