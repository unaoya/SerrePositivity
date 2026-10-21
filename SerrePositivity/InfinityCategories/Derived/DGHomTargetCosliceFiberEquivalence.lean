module
public import SerrePositivity.InfinityCategories.Derived.DGFunctorClosedCosliceComparison
public import SerrePositivity.InfinityCategories.Derived.DGHomTargetUnitLiftComparison
/-!
概要：同じ Hom 単位の元の実 coslice 比較は、全ての実 fiber で同値。
方針：同じ合成 Hom 鎖写像が dg Yoneda の逆であることを、元の実 fiber 判定へ適用する。
規約：点ごとの抽象空間同値ではなく、構成済みの同じ実 fiber 射を証明する。
使われ方：Hom の pointed 表示の全 fiber 同値と全関手比較への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C] (x y : C)
/-- 同じ Hom 単位から構成した元の実 coslice 比較は、各実対象上の fiber で全空間同値。 -/
lemma dgHomTargetCosliceComparison_fiber_isQCatEquivalence :
    IsQCatEquivalence (transportSquareFiberMap
      (sliceUnderProjection ((SSet.yonedaEquiv (X := dgNerve R C)).symm (Simplex.vertex x)))
      (sliceUnderProjection (SSet.yonedaEquiv.symm (dgHomModuleUnitVertex R C)))
      (dgHomTargetCosliceComparison R C x) (dgNerve.map (dgHomTargetModuleLift R C x))
      (dgHomTargetCosliceComparison_projection R C x) (Simplex.vertex y)) := by
  let := dgHomTargetUnitLiftHomMap_isIso R C x y
  exact dgFunctorClosedCosliceRawFiber_isQCatEquivalence R (dgHomTargetModuleLift R C x)
    x (dgHomModuleUnit R C) y
    ((dgUniverseLiftUp.{u, u + 1, max (u + 1) v} R (RightModule R PUnit.{1})).onClosed.map
      (dgHomTargetUnit R C x))
/-- 同じ実 coslice 比較の全ての実頂点 fiber 射は全空間同値。 -/
lemma dgHomTargetCosliceComparison_fibers_isQCatEquivalence (b : (dgNerve R C) _⦋0⦌) :
    IsQCatEquivalence (transportSquareFiberMap
      (sliceUnderProjection ((SSet.yonedaEquiv (X := dgNerve R C)).symm (Simplex.vertex x)))
      (sliceUnderProjection (SSet.yonedaEquiv.symm (dgHomModuleUnitVertex R C)))
      (dgHomTargetCosliceComparison R C x) (dgNerve.map (dgHomTargetModuleLift R C x))
      (dgHomTargetCosliceComparison_projection R C x) b) := by
  obtain ⟨z, rfl⟩ := (Simplex.vertexEquiv (A := R) (D := C)).symm.surjective b
  exact dgHomTargetCosliceComparison_fiber_isQCatEquivalence R C x z
end SerrePositivity.InfinityCategories
