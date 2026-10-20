module
public import SerrePositivity.InfinityCategories.Derived.DGVerdierRightKanDiagram
public import SerrePositivity.InfinityCategories.Derived.DGVerdierOverLimit
public import SerrePositivity.InfinityCategories.Derived.CosliceInitialRealization
public import SerrePositivity.InfinityCategories.Derived.RelativeRoofComparisonCofinality
public import SerrePositivity.InfinityCategories.Derived.DGActualRoofWeakEquivalence
/-!
概要：実逆分母から Drinfeld 商の実右 Kan 形状への比較は left cofinal。
方針：既証明の同じ実屋根比較を各 Quillen A の全 slice に基底変換する。
規約：商の反転性・実屋根の cofinality・実添字の弱可縮性を実際に使用する。
使われ方：任意 quasicategory 標的での右 Kan 局所極限と局所化普遍性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]
/-- 既証明の実屋根比較の left cofinality を、後合成のままの同じ raw 表示へ移す。 -/
lemma dgRawRoofFunctorMap_isLeftCofinal (P : Set D) (hP : DGQuotient.localKFlat A D P)
    (x y : D) : IsLeftCofinal (rawRoofFunctorMap (dgQuotientNerveProjection A D P)
      (dgVerdierOverSource A D P x) (SSet.yonedaEquiv.symm (Simplex.vertex y))) := by
  apply (roofComparisonTransport_isLeftCofinal_iff (dgQuotientNerveProjection A D P)
    (dgVerdierOverSource A D P x) _ _ _ (dgQuotientNervePoint A D P y) rfl).mp
  exact dgRoofCorrespondenceMap_isLeftCofinal A D P hP x y
/-- 実逆分母の coherent な coslice 実現から、商の右 Kan 形状への実比較は left cofinal。 -/
lemma dgVerdierRightKanMap_isLeftCofinal (P : Set D) (hP : DGQuotient.localKFlat A D P)
    (x : D) (R : DGVerdierRightKanDiagram A D P hP x) :
    IsLeftCofinal (dgVerdierRightKanMap A D P hP x R) := by
  apply isLeftCofinal_of_relativeRoofComparisons
  · intro c
    apply (relativeRoofComparison_isLeftCofinal_iff_raw _ _ _ _).mpr
    change IsLeftCofinal (rawRoofFunctorMap (dgQuotientNerveProjection A D P)
      (dgVerdierRightKanMap A D P hP x R ≫ rightKanProjection
        (dgQuotientNerveProjection A D P) (Simplex.vertex ((DGQuotient.inclusion A D P).obj x)))
      (SSet.yonedaEquiv.symm c ≫ rightKanProjection (dgQuotientNerveProjection A D P)
        (Simplex.vertex ((DGQuotient.inclusion A D P).obj x))))
    rw [dgVerdierRightKanMap_projection]
    let y := (dgNerve.vertexEquiv A D)
      ((rightKanProjection (dgQuotientNerveProjection A D P)
        (Simplex.vertex ((DGQuotient.inclusion A D P).obj x))).app (Opposite.op ⦋0⦌) c)
    have hp : SSet.yonedaEquiv.symm c ≫ rightKanProjection (dgQuotientNerveProjection A D P)
        (Simplex.vertex ((DGQuotient.inclusion A D P).obj x)) =
          SSet.yonedaEquiv.symm (Simplex.vertex y) := by
      apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv.apply_symm_apply,
        SSet.yonedaEquiv.apply_symm_apply]
      exact ((dgNerve.vertexEquiv A D).symm_apply_apply _).symm
    rw [hp]
    exact dgRawRoofFunctorMap_isLeftCofinal A D P hP x y
  · intro i
    change IsInitialVertex
      ((dgVerdierRightKanMap A D P hP x R ≫ pullback.fst _ _).app (Opposite.op ⦋0⦌) i)
    rw [dgVerdierRightKanMap_coslice]
    apply CosliceHomotopyRealization.isInitialVertex R
    intro a
    exact simplicialHomotopyOfFunctorEdge_vertex_isInvertible
      (FunctorIso.edge (dgVerdierOverQuotientEvaluationIso A D P hP x).symm)
      (FunctorIso.edge_isInvertible (dgVerdierOverQuotientEvaluationIso A D P hP x).symm) a
  · exact dgVerdierOver_isWeaklyContractible A D P x
end SerrePositivity.InfinityCategories
