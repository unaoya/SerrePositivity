module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.LastPostcomposition
/-!
概要：任意次数の後合成を、HA の符号付き削除項と切断項の差へ分配する。
方針：既存の斉次合成の線形性と全次数の結合則を使う。
規約：後合成射の次数を零に限定せず、閉性も仮定しない。
使われ方：混合 HA の元の単体側の和を、高次 Hom の Leibniz 項へ因数分解する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory DifferentialGraded
variable {R : Type u} [CommRing R] {C : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]

lemma dgCoherentBarHom_postcompose_signed_difference {X M B Y : C} {p q r : ℤ}
    (f : _root_.SerrePositivity.DifferentialGraded.GradedHom R X M p) (g : _root_.SerrePositivity.DifferentialGraded.GradedHom R M B q)
    (e : _root_.SerrePositivity.DifferentialGraded.GradedHom R X B (p + q)) (ρ : _root_.SerrePositivity.DifferentialGraded.GradedHom R B Y r) (c : ℤˣ) :
    _root_.SerrePositivity.DifferentialGraded.compose R ρ (c • (e - _root_.SerrePositivity.DifferentialGraded.compose R g f rfl)) rfl =
      c • (_root_.SerrePositivity.DifferentialGraded.compose R ρ e rfl -
        _root_.SerrePositivity.DifferentialGraded.compose R (_root_.SerrePositivity.DifferentialGraded.compose R ρ g rfl) f (show p + (q + r) = p + q + r by omega)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_units_smul_right, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sub_right,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum f g ρ rfl rfl rfl]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
