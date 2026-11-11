module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.PushoutRetracts
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.DiagramOppositeRetracts
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.SquareOpposite

/-!
概要：全四角形の関手 ∞ 圏内の元の引き戻し四角形の retract は引き戻し。
方針：元の全図式と添字を反転し、反転四角形への制限で押し出しの閉性を使う。
規約：元の同じ全四角形の普遍性を結論する。
使われ方：完備化の双カルテジアンな零角四角形の coherent 分裂。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の引き戻し四角形の全関手 ∞ 圏内の指定 retract は、同じ全四角形で引き戻し。 -/
lemma isPullbackSquare_of_diagram_retract {X : SSet.{u}} [Quasicategory X]
    (F G : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X)
    (r : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.VertexRetraction (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)) (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F := by
  let j : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ ((Δ[1] : SSet.{u}) ⊗ Δ[1]).op :=
    (((stdSimplex.opIso ⦋1⦌).inv ▷ Δ[1]) ≫
      ((Δ[1] : SSet.{u}).op ◁ (stdSimplex.opIso ⦋1⦌).inv)) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.opTensorIso Δ[1] Δ[1]).hom
  have ho := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.diagram_retract_op F G ⟨r⟩
  have hr := ho.map ((pre j).app X.op)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid G)) at hr
  exact (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isPullbackSquare_iff_reverseGrid F).mpr
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.isPushoutSquare_of_diagram_retract (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid F) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid G) hr.some
      ((_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isPullbackSquare_iff_reverseGrid G).mp hG))

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
