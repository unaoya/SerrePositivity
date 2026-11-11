module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGHomTargetSpaceComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGHomTargetPointedFiberEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCosliceYonedaPointedDisplay
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSemifreeHomTargetPointedDisplay
/-!
概要：半自由加群の固定始点 Hom を元の F1 Hom∞ の関手族へ比較する。
方針：同じ coslice の全 fiber 比較と transport 表現の比較を特殊化する。
規約：D(R) 値 Hom の同じ augmentation と厳密切断を使う。
使われ方：固定始点の全関手比較と二変数 Hom の統合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
/-- 半自由 Hom の同じ実 pointed 表示の各実 fiber 射は同値。 -/
lemma dgSemifreeHomTargetCoslicePointedFiber_isQCatEquivalence (P Q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomTargetCoslicePointedFiber R D P Q) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetCoslicePointedDisplay_fiber_isQCatEquivalence R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)
    P (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Q)
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomTargetCoslicePointedFiber, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomTargetCoslicePointedDisplay,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetUnderlyingSpaceInfinity_semifree] using! h
/-- 元の F1 二変数 Hom∞ の第一変数を同じ半自由加群に固定した全関手。 -/
def dgSemifreeHomTargetF1SpaceInfinity (P : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{max (u + 1) v} :=
  CartesianMonoidalCategory.lift
    (SSet.const (ULift.up (SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomVertex R D P)))) (𝟙 _) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomSpaceInfinity R D
/-- 元の二変数 Hom∞ の制限は同じ F1 Yoneda 評価そのもの。 -/
lemma dgSemifreeHomTargetF1SpaceInfinity_eq_yoneda (P : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    dgSemifreeHomTargetF1SpaceInfinity R D P =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCosliceYonedaSpaceInfinity (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomVertex R D P) := by
  symm
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCosliceYonedaSpaceInfinity, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.curry_evaluateFunctorAt_vertex]
  rfl
/-- 実全 Hom の基礎空間関手と元の F1 固定始点 Hom∞ の全関手同型。 -/
def dgSemifreeHomTargetSpaceComparisonIso (P : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomTargetSpaceInfinity R D P)
      (dgSemifreeHomTargetF1SpaceInfinity R D P) := by
  rw [dgSemifreeHomTargetF1SpaceInfinity_eq_yoneda]
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetUnderlyingSpaceInfinity_semifree] using!
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetSpaceComparisonIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) P)
/-- 実 D(R) 値 Hom の基礎空間関手と元の F1 Hom∞ の全関手同型。 -/
def dgSemifreeDerivedHomTargetF1SpaceIso (P : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomTargetSpaceInfinity R D P)
      (dgSemifreeHomTargetF1SpaceInfinity R D P) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomTargetSpaceIso R D P ≪≫ dgSemifreeHomTargetSpaceComparisonIso R D P
end SerrePositivity.InfinityCategories.Project.DerivedCategories
