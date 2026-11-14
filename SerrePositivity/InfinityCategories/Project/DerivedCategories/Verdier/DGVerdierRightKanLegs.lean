module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierRightKanCanonical
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierOverLimitLegs
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.ConeLegRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightConstantFamily
/-!
概要：任意反転関手の商の右 Kan 局所極限錐は、実逆分母の各指定値で同じ脚が可逆。
方針：cofinal な実分母制限を元の全図式へ厳密に戻し、実分母極限錐の脚を回収する。
規約：選ばれた実逆分母図式と全頂点を保持。使われ方：任意右 Kan 単位の同じ実成分の可逆性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
/-- 実右 Kan 極限錐の同じ実逆分母における脚は、元の同じ実辺として可逆。 -/
lemma dgVerdierRightKanLimitCone_leg_isInvertible (P : Set D)
    (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P) (x : D) {Y : SSet.{max u v}} [Quasicategory Y]
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P))
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P) F
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((DGQuotient.inclusion A D P).obj x)))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c)
    (R : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierRightKanDiagram A D P hP x) (i : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg c
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierRightKanMap A D P hP x R).app (Opposite.op ⦋0⦌) i)) := by
  let u := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierRightKanMap A D P hP x R
  have hu := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierRightKanMap_isLeftCofinal A D P hP x R
  have he : u ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P) F
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((DGQuotient.inclusion A D P).obj x)) =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x ≫ F := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierRightKanMap_projection]
  let d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x ≫ F) :=
    ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone c u).val, (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone c u).property.trans he⟩
  have hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanIsLimitCone_congr he (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone c u) d rfl).mp
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLimitCone_iff_restrict_of_leftCofinal u hu _ c).mp hc)
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverLimitCone_leg_isInvertible A D P x F hF d hd i
  have he' : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg d i).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg c (u.app (Opposite.op ⦋0⦌) i)).edge := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.nativeConeLeg_restrict_edge c u i
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he').mp h
end SerrePositivity.InfinityCategories.Project.DerivedCategories
