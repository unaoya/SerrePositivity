module
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut

/-! # dg 加群の標的の −1 shift の Hom 座標

概要：shift した標的への次数 n+1 の全 Hom 成分を元の標的への次数 n と同定する。
方針：閉斉次単位とその逆を合成し、全 Hom end の線形性と符号付き微分を確認する。
規約：二つの写像は微分と反可換。使われ方：β3 の Hom into shifted cone の座標。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- 標的の −1 shift を実際の閉斉次単位で外す全次数線形同値。 -/
def dgModuleNegativeShiftTargetHomEquiv (X M : _root_.SerrePositivity.DifferentialGraded.RightModule A D) (n : ℤ) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom A X (shiftModule (-1) M) (n + 1) ≃ₗ[A] _root_.SerrePositivity.DifferentialGraded.GradedHom A X M n where
  toFun z := compose A (moduleShiftOutElement A D (-1) M) z (by omega)
  invFun z := compose A (moduleShiftInElement A D (-1) M) z rfl
  left_inv z := by
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum (A := A) z (moduleShiftOutElement A D (-1) M)
      (moduleShiftInElement A D (-1) M) (show (n + 1) + (-1) = n by omega)
      (show (-1) + (-(-1)) = 0 by decide) rfl
    rw [moduleShiftOutIn, unit_compose] at h
    exact h
  right_inv z := by
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum (A := A) z (moduleShiftInElement A D (-1) M)
      (moduleShiftOutElement A D (-1) M) rfl (show -(-1) + (-1) = 0 by decide)
      (show n + 1 + (-1) = n by omega)
    rw [moduleShiftInOut, unit_compose] at h
    exact h
  map_add' z w := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_add_right _ _ _ _
  map_smul' c z := by
    apply moduleHomElement_ext A D
    intro x
    simp only [moduleHomCompose_π, map_smul, RingHom.id_apply]
    exact CochainComplex.HomComplex.Cochain.smul_comp _ _ _ _

/-- shift を外す Hom 座標は微分と反可換。 -/
lemma dgModuleNegativeShiftTargetHomEquiv_differential (X M : _root_.SerrePositivity.DifferentialGraded.RightModule A D) (n : ℤ)
    (z : _root_.SerrePositivity.DifferentialGraded.GradedHom A X (shiftModule (-1) M) (n + 1)) :
    _root_.SerrePositivity.DifferentialGraded.differential A (dgModuleNegativeShiftTargetHomEquiv A D X M n z) =
      -dgModuleNegativeShiftTargetHomEquiv A D X M (n + 1) (differential A z) := by
  change _root_.SerrePositivity.DifferentialGraded.differential A (compose A (moduleShiftOutElement A D (-1) M) z (by omega)) = _
  rw [_root_.SerrePositivity.DifferentialGraded.differential_compose, show differential (D := RightModule A D) A
    (moduleShiftOutElement A D (-1) M) = 0 from moduleShiftOutElement_d A D (-1) M,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, zero_add]
  simp only [Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul]
  rfl

/-- shift を入れる逆 Hom 座標も微分と反可換。 -/
lemma dgModuleNegativeShiftTargetHomEquiv_symm_differential (X M : _root_.SerrePositivity.DifferentialGraded.RightModule A D) (n : ℤ)
    (z : _root_.SerrePositivity.DifferentialGraded.GradedHom A X M n) :
    _root_.SerrePositivity.DifferentialGraded.differential A ((dgModuleNegativeShiftTargetHomEquiv A D X M n).symm z) =
      -(dgModuleNegativeShiftTargetHomEquiv A D X M (n + 1)).symm (differential A z) := by
  change _root_.SerrePositivity.DifferentialGraded.differential A (compose A (moduleShiftInElement A D (-1) M) z rfl) = _
  rw [_root_.SerrePositivity.DifferentialGraded.differential_compose, show differential (D := RightModule A D) A
    (moduleShiftInElement A D (-1) M) = 0 from moduleShiftInElement_d A D (-1) M,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, zero_add]
  simp only [show -(-1 : ℤ) = 1 from by decide, Int.negOnePow_one,
    Units.neg_smul, one_smul]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
