module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierRightKanDiagram
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierOverLimit
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.CosliceInitialRealization
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.RelativeRoofComparisonCofinality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGActualRoofWeakEquivalence
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
/-- 既証明の実屋根比較の left cofinality を、後合成のままの同じ raw 表示へ移す。 -/
lemma dgRawRoofFunctorMap_isLeftCofinal (P : Set D) (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    (x y : D) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.rawRoofFunctorMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x) (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y))) := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofComparisonTransport_isLeftCofinal_iff (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x) _ _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNervePoint A D P y) rfl).mp
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap_isLeftCofinal A D P hP x y
/-- 実逆分母の coherent な coslice 実現から、商の右 Kan 形状への実比較は left cofinal。 -/
lemma dgVerdierRightKanMap_isLeftCofinal (P : Set D) (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    (x : D) (R : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierRightKanDiagram A D P hP x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierRightKanMap A D P hP x R) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.isLeftCofinal_of_relativeRoofComparisons
  · intro c
    apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.relativeRoofComparison_isLeftCofinal_iff_raw _ _ _ _).mpr
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.rawRoofFunctorMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierRightKanMap A D P hP x R ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanProjection
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((DGQuotient.inclusion A D P).obj x)))
      (SSet.yonedaEquiv.symm c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanProjection (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((DGQuotient.inclusion A D P).obj x))))
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierRightKanMap_projection]
    let y := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A D)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanProjection (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((DGQuotient.inclusion A D P).obj x))).app (Opposite.op ⦋0⦌) c)
    have hp : SSet.yonedaEquiv.symm c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanProjection (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((DGQuotient.inclusion A D P).obj x)) =
          SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y) := by
      apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv.apply_symm_apply,
        SSet.yonedaEquiv.apply_symm_apply]
      exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A D).symm_apply_apply _).symm
    rw [hp]
    exact dgRawRoofFunctorMap_isLeftCofinal A D P hP x y
  · intro i
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierRightKanMap A D P hP x R ≫ pullback.fst _ _).app (Opposite.op ⦋0⦌) i)
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierRightKanMap_coslice]
    apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.CosliceHomotopyRealization.isInitialVertex R
    intro a
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.simplicialHomotopyOfFunctorEdge_vertex_isInvertible
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.edge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverQuotientEvaluationIso A D P hP x).symm)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.edge_isInvertible (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverQuotientEvaluationIso A D P hP x).symm) a
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver_isWeaklyContractible A D P x
end SerrePositivity.InfinityCategories.Project.DerivedCategories
