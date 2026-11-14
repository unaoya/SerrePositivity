module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NativeHomCriterion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGModuleKappaCompactProjectiveComparison
/-!
概要：代表可能加群そのものの射影的頂点で、native compact 性を全 Hom 保存へ接続する。
方針：半自由分解との QCat 同値で compact 性を輸送し、同じ全 Hom 関手を比較する。
規約：射影性は実加群の Hom 計算にのみ使い、ordinary compact 性は仮定しない。
使われ方：coherent な評価交換を representable の c2 へ代入する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]

/-- 同じ代表可能加群を、全 Hom end の意味で射影的な実対象として保持する。 -/
def dgBarCompactRepresentableProjective (x : D) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D :=
  ⟨_root_.SerrePositivity.DifferentialGraded.representable R x, _root_.SerrePositivity.DifferentialGraded.representable_homotopicallyProjective R D x⟩

/-- 射影的模型の同じ全 Hom 空間関手と、元の共変代表関手の全同型。 -/
def dgBarCompactProjectiveHomIso (P : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetUnderlyingSpaceInfinity R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D) P)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity (C := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleNerve R D)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := R) P)) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactHomIso.{u, v} R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D) P

/-- 同じ代表加群の分解頂点の native compact 性を、代表そのものの全 Hom 保存で判定。 -/
lemma dgBarCompactRepresentable_iff_hom_preserves (κ : Cardinal.{u}) (x : D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ (ForgetEnrichment.of (Complex R) (representable R x)) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesKappaFilteredColimits.{u, max (u + 1) v} κ
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetUnderlyingSpaceInfinity R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D)
          (dgBarCompactRepresentableProjective R D x)) := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact_iff_projectiveVertex R D
    (dgBarCompactRepresentableProjective R D x)).trans
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompact_iff_hom_preserves.{u, v} R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D) κ
        (dgBarCompactRepresentableProjective R D x))

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
