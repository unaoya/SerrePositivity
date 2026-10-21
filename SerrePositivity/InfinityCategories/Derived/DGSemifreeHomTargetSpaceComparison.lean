module
public import SerrePositivity.InfinityCategories.Derived.DGHomTargetSpaceComparison
public import SerrePositivity.InfinityCategories.Derived.DGHomTargetPointedFiberEquivalence
public import SerrePositivity.InfinityCategories.Derived.DGCosliceYonedaPointedDisplay
public import SerrePositivity.InfinityCategories.Derived.DGSemifreeHomTargetPointedDisplay
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
/-- 半自由 Hom の同じ実 pointed 表示の各実 fiber 射は同値。 -/
lemma dgSemifreeHomTargetCoslicePointedFiber_isQCatEquivalence (P Q : SemifreeDGModules R D) :
    IsQCatEquivalence (dgSemifreeHomTargetCoslicePointedFiber R D P Q) := by
  have h := dgHomTargetCoslicePointedDisplay_fiber_isQCatEquivalence R (SemifreeDGModules R D)
    P (Simplex.vertex Q)
  simpa only [dgSemifreeHomTargetCoslicePointedFiber, dgSemifreeHomTargetCoslicePointedDisplay,
    dgHomTargetUnderlyingSpaceInfinity_semifree] using! h
/-- 元の F1 二変数 Hom∞ の第一変数を同じ半自由加群に固定した全関手。 -/
def dgSemifreeHomTargetF1SpaceInfinity (P : SemifreeDGModules R D) :
    (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
      (dgModuleDerivedInfinityCategory R D) ⟶ SpaceInfinity.{max (u + 1) v} :=
  CartesianMonoidalCategory.lift
    (SSet.const (ULift.up (SSet.opObjEquiv.symm (dgSemifreeHomVertex R D P)))) (𝟙 _) ≫
      dgModuleHomSpaceInfinity R D
/-- 元の二変数 Hom∞ の制限は同じ F1 Yoneda 評価そのもの。 -/
lemma dgSemifreeHomTargetF1SpaceInfinity_eq_yoneda (P : SemifreeDGModules R D) :
    dgSemifreeHomTargetF1SpaceInfinity R D P =
      dgCosliceYonedaSpaceInfinity (dgModuleDerivedInfinityCategory R D)
        (dgSemifreeHomVertex R D P) := by
  symm
  rw [dgCosliceYonedaSpaceInfinity, yonedaInfinityMap, curry_evaluateFunctorAt_vertex]
  rfl
/-- 実全 Hom の基礎空間関手と元の F1 固定始点 Hom∞ の全関手同型。 -/
def dgSemifreeHomTargetSpaceComparisonIso (P : SemifreeDGModules R D) :
    FunctorIso (dgSemifreeHomTargetSpaceInfinity R D P)
      (dgSemifreeHomTargetF1SpaceInfinity R D P) := by
  rw [dgSemifreeHomTargetF1SpaceInfinity_eq_yoneda]
  simpa only [dgHomTargetUnderlyingSpaceInfinity_semifree] using!
    (dgHomTargetSpaceComparisonIso R (SemifreeDGModules R D) P)
/-- 実 D(R) 値 Hom の基礎空間関手と元の F1 Hom∞ の全関手同型。 -/
def dgSemifreeDerivedHomTargetF1SpaceIso (P : SemifreeDGModules R D) :
    FunctorIso (dgSemifreeDerivedHomTargetSpaceInfinity R D P)
      (dgSemifreeHomTargetF1SpaceInfinity R D P) :=
  dgSemifreeDerivedHomTargetSpaceIso R D P ≪≫ dgSemifreeHomTargetSpaceComparisonIso R D P
end SerrePositivity.InfinityCategories
