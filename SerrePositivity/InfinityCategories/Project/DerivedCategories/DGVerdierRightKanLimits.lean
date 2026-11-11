module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierRightKanCofinality
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalLimitTransfer
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightExistence
/-!
概要：任意の実分母反転関手について、商の全頂点で実右 Kan 局所極限を構成する。
方針：実逆分母の left cofinal 比較に沿って、実分母図式の既存極限を移送する。
規約：標的は任意 quasicategory。使われ方：全関手の右 Kan 拡張による組み立て。
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
/-- 元の対象の商像で、任意反転関手の実右 Kan 局所図式は極限を持つ。 -/
lemma dgVerdierRightKanDiagram_hasLimit (P : Set D) (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    (x : D) {Y : SSet.{max u v}} [Quasicategory Y] (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P) F
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((DGQuotient.inclusion A D P).obj x))) := by
  obtain ⟨R⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierRightKanDiagram_nonempty A D P hP x
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.hasLimit_of_leftCofinal (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierRightKanMap A D P hP x R)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierRightKanMap_isLeftCofinal A D P hP x R)
  have he : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierRightKanMap A D P hP x R ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P) F
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((DGQuotient.inclusion A D P).obj x)) =
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x ≫ F := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierRightKanMap_projection]
  exact (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit he).mpr (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver_hasLimit A D P x F hF)
/-- 任意反転関手の商の全頂点で、実右 Kan 局所極限が存在する。 -/
lemma dgVerdierRightKanDiagram_hasLimit_all (P : Set D) (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    {Y : SSet.{max u v}} [Quasicategory Y] (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P)) (z : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P) F z) := by
  let x := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (DGQuotient.QuotientObject D P)) z
  have hz : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x = z := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A _).symm_apply_apply z
  have h := dgVerdierRightKanDiagram_hasLimit A D P hP x.val F hF
  exact (congrArg (fun t => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P) F t)) hz).mp h
/-- 任意反転関手は、全商図式と実単位ホモトピーを持つ実右 Kan 拡張へ組み立つ。 -/
lemma dgVerdierInvertingFunctor_rightKanExtension_exists (P : Set D)
    (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P) {Y : SSet.{max u v}} [Quasicategory Y]
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P)) :
    ∃ (G : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P ⟶ Y) (α : SSet.Homotopy
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P ≫ G) F),
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P) F G α :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanRightExtension_of_local_limits (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P) F
    (dgVerdierRightKanDiagram_hasLimit_all A D P hP F hF)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
