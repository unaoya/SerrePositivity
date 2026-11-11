module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NativeEvaluationPiData
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.FilteredSpaceBridge
/-!
概要：実評価空間関手は、全 native κ-filtered coherent 余極限を保存する。
方針：元の bar の五条件を Ind-π の実判定へ代入し、poset 帰着を使う。
規約：κ と添字宇宙を保ち、strict 比較や保存性を仮定として残さない。
使われ方：representable とその生成閉包の native κ-compact 性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  (κ : Cardinal.{u}) [Fact κ.IsRegular]

/-- 全 native κ-filtered 図式についての実評価空間の保存性。 -/
lemma dgBarCompactEvaluation_preserves (x : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesKappaFilteredColimits.{u, max (u + 1) v} κ
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactProjectiveEvaluationSpaceInfinity R D x) := by
  apply _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluation_preserves_of_bridge_and_posetPi R D x
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.dgBarCompactFilteredSpacePiBridge κ)
  intro I hI hFiltered G
  letI : IsFiltered I := isFiltered_of_isCardinalFiltered I κ
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactNativeEvaluationPiData R D G x

/-- 同じ代表そのものの native κ-compact 性。 -/
lemma dgBarCompactRepresentable_isKappaCompact (x : D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ (ForgetEnrichment.of (Complex R) (representable R x)) :=
  (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactRepresentable_iff_evaluation_preserves R D κ x).mpr
    (dgBarCompactEvaluation_preserves R D κ x)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
