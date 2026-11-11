module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierOverEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CosliceHomotopyRealization
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.Shapes
/-!
概要：実 Verdier 分母の coherent な逆像図式を、商関手の実右 Kan 形状へ送る。
方針：商内の全添字の評価同型を反転し、同じ全ホモトピーを coslice に持ち上げる。
規約：元の始域射影と厳密に可換。cofinality は別に証明する。
使われ方：任意反転関手の右 Kan 拡張の各点の極限の構成。
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
variable (P : Set D) (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P) (x : D)
/-- 実分母の商像の同じ全添字の逆を表す、coslice 内の実図式と全 prism。 -/
abbrev DGVerdierRightKanDiagram :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.CosliceHomotopyRealization (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((DGQuotient.inclusion A D P).obj x))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.simplicialHomotopy
      (X := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet)) (Y := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P)
      (f := SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((DGQuotient.inclusion A D P).obj x)))
      (g := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverQuotientEvaluationIso A D P hP x).symm)
/-- 実分母の逆の全添字図式を、同じ元の始域を持つ実右 Kan 形状へ送る。 -/
def dgVerdierRightKanMap (R : DGVerdierRightKanDiagram A D P hP x) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanShape (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((DGQuotient.inclusion A D P).obj x)) :=
  pullback.lift R.diagram (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x) R.projection
/-- 右 Kan 形状への実逆分母写像は、元の始域射影を厳密に保つ。 -/
lemma dgVerdierRightKanMap_projection (R : DGVerdierRightKanDiagram A D P hP x) :
    dgVerdierRightKanMap A D P hP x R ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanProjection (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((DGQuotient.inclusion A D P).obj x)) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x :=
  pullback.lift_snd _ _ _
/-- 右 Kan 形状への実逆分母写像は、指定した coherent な coslice 図式を保持する。 -/
lemma dgVerdierRightKanMap_coslice (R : DGVerdierRightKanDiagram A D P hP x) :
    dgVerdierRightKanMap A D P hP x R ≫ pullback.fst _ _ = R.diagram :=
  pullback.lift_fst _ _ _
/-- 実 Verdier 分母の逆を、元の始域と全区間を保って右 Kan 形状内に同時に実現できる。 -/
lemma dgVerdierRightKanDiagram_nonempty : Nonempty (DGVerdierRightKanDiagram A D P hP x) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cosliceHomotopyRealization_nonempty _ _ _
end SerrePositivity.InfinityCategories.Project.DerivedCategories
