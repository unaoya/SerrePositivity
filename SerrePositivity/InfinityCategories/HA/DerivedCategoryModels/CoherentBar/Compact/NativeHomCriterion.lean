module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSemifreeHomTargetSpaceComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCosliceYonedaOppositeComparison
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.RepresentableCoslice
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.Preservation
/-!
概要：半自由加群の native κ-compact 性を全 Hom 空間関手の余極限保存で判定する。
方針：同じ coslice の分類比較を介し、実 Hom の全関手同型を共変代表へ合成する。
規約：試験対象は全 native κ-filtered 図式。strict 図式への制限は行わない。
使われ方：coherent bar の評価比較を c2 の定義へ代入する消費入口。
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

/-- 任意の dg 模型の実 Hom 空間関手を、同じ頂点の共変代表へ比較する。 -/
def dgBarCompactHomIso (C : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] (x : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetUnderlyingSpaceInfinity R C x)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity (C := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := R) x)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetSpaceComparisonIso R C x ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCosliceYonedaClassificationIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := R) x) ≪≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.covariantRepresentableInfinity_cosliceIso (C := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := R) x)).symm

/-- 全 native 図式での実 Hom 保存と同じ頂点の compact 性の一般判定。 -/
lemma dgBarCompact_iff_hom_preserves (C : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
    (κ : Cardinal.{u}) (x : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, max (u + 1) v} (C := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C) κ
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := R) x) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesKappaFilteredColimits.{u, max (u + 1) v} κ
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetUnderlyingSpaceInfinity R C x) := by
  constructor
  · intro h
    exact h.of_functorIso (dgBarCompactHomIso R C x).symm
  · intro h
    exact h.of_functorIso (dgBarCompactHomIso R C x)

/-- 実半自由 Hom の全空間関手と compact 性の定義にある元の共変代表の比較。 -/
def dgBarCompactNativeHomIso (P : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomTargetSpaceInfinity R D P)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomVertex R D P)) := by
  have e := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomTargetF1SpaceIso R D P
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomTargetF1SpaceInfinity_eq_yoneda] at e
  exact e ≪≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCosliceYonedaClassificationIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomVertex R D P) ≪≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.covariantRepresentableInfinity_cosliceIso
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomVertex R D P)).symm

/-- 全 native 図式での実 Hom 空間の余極限保存は、同じ頂点の native compact 性と同値。 -/
lemma dgBarCompact_iff_nativeHom_preserves (κ : Cardinal.{u}) (P : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, max (u + 1) v}
        κ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomVertex R D P) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesKappaFilteredColimits.{u, max (u + 1) v}
        κ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomTargetSpaceInfinity R D P) := by
  constructor
  · intro h
    exact h.of_functorIso (dgBarCompactNativeHomIso R D P).symm
  · intro h
    exact h.of_functorIso (dgBarCompactNativeHomIso R D P)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
