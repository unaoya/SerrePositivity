module
public import SerrePositivity.InfinityCategories.Derived.DGHomTargetPointedDisplay
public import SerrePositivity.InfinityCategories.Derived.DGSemifreeHomSpaceComparison
/-!
概要：同じ Hom 単位の実 pointed 表示を、公開済みの半自由 Hom 関手族へ接続する。
方針：二つの全関手が厳密に同じことを確認し、同じ射影と実 fiber 射を公開する。
規約：全 fiber の同値性は別工程。使われ方：元の F1 Hom 関手族との比較。
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
/-- 一般の構成は、公開済みの同じ半自由 Hom の空間値全関手そのもの。 -/
lemma dgHomTargetUnderlyingSpaceInfinity_semifree (P : SemifreeDGModules R D) :
    dgHomTargetUnderlyingSpaceInfinity R (SemifreeDGModules R D) P =
      dgSemifreeHomTargetSpaceInfinity R D P := by
  rfl
/-- 元の同じ半自由 Hom の実 coslice 全体からの pointed 表示。 -/
def dgSemifreeHomTargetCoslicePointedDisplay (P : SemifreeDGModules R D) :
    (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
      (dgVertexCoslice R (SemifreeDGModules R D) P) ⟶
        PointedSpaceInfinity.{max (u + 1) v} :=
  dgHomTargetCoslicePointedDisplay R (SemifreeDGModules R D) P
/-- 同じ pointed 表示の底は、公開済みの同じ全空間値 Hom 関手。 -/
lemma dgSemifreeHomTargetCoslicePointedDisplay_projection (P : SemifreeDGModules R D) :
    dgSemifreeHomTargetCoslicePointedDisplay R D P ≫ pointedSpaceProjection =
      (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
        (sliceUnderProjection ((SSet.yonedaEquiv (X := dgModuleDerivedInfinityCategory R D)).symm
          (dgSemifreeHomVertex R D P))) ≫ dgSemifreeHomTargetSpaceInfinity R D P := by
  rw [dgSemifreeHomTargetCoslicePointedDisplay, dgHomTargetCoslicePointedDisplay_projection,
    dgHomTargetUnderlyingSpaceInfinity_semifree]
/-- 同じ全比較が誘導する、各指定終点上の実 fiber 射。 -/
def dgSemifreeHomTargetCoslicePointedFiber (P Q : SemifreeDGModules R D) :=
  transportSquareFiberMap
    ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
      (sliceUnderProjection ((SSet.yonedaEquiv (X := dgModuleDerivedInfinityCategory R D)).symm
        (dgSemifreeHomVertex R D P)))) pointedSpaceProjection
    (dgSemifreeHomTargetCoslicePointedDisplay R D P) (dgSemifreeHomTargetSpaceInfinity R D P)
    (dgSemifreeHomTargetCoslicePointedDisplay_projection R D P)
    (ULift.up (dgSemifreeHomVertex R D Q))
end SerrePositivity.InfinityCategories
