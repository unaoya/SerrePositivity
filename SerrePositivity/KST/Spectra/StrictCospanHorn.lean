module

public import SerrePositivity.KST.Spectra.CospanNerveHornIso
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FunctorComparison.LiftedShapeNerveIso
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Edges
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FiniteShapes

/-!
概要：通常の cospan の coherent な表示を二辺のホーン上で計算する。
方針：持ち上げた nerve とホーンの同型を用い、両枝で元の射の辺を照合する。
規約：対象・射の宇宙は独立。使われ方：任意の coherent cospan の極限への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.CospanShape

/-- 通常の小さい cospan の持ち上げた nerve と二辺のホーンの厳密な同型。 -/
def strictCospanHornIso :
    (SSet.uliftFunctor.{v, u}).obj (nerve (AsSmall.{u} WalkingCospan)) ≅
      (horn 2 2 : SSet.{max u v}) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.liftedAsSmallNerveIso WalkingCospan ≪≫ cospanNerveHornIso

variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
  {E X B : C} (f : E ⟶ B) (g : X ⟶ B)

/-- 同じ宇宙へ持ち上げた cospan の通常の nerve による表示。 -/
lemma strictDiagram_shape :
    strictCospanHornIso.inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (AsSmall.down ⋙ cospan f g) =
      hornToCospanNerve ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.resizedNerveMap (AsSmall.down ⋙ cospan f g) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  rfl

/-- ホーン上の左辺は元の左射の coherent な辺。 -/
lemma strictDiagram_left :
    horn₂₂.ι₀₂ ≫ strictCospanHornIso.inv ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (AsSmall.down ⋙ cospan f g) =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge := by
  rw [strictDiagram_shape, ← Category.assoc, hornToCospanNerve_left_edge]
  apply SSet.yonedaEquiv.injective
  simp only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C).app (Opposite.op ⦋1⦌) _ =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ f)
  apply congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C).app _)
  refine ComposableArrows.ext₁ rfl rfl ?_
  change f = 𝟙 _ ≫ f ≫ 𝟙 _
  simp

/-- ホーン上の右辺は元の右射の coherent な辺。 -/
lemma strictDiagram_right :
    horn₂₂.ι₁₂ ≫ strictCospanHornIso.inv ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (AsSmall.down ⋙ cospan f g) =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g).edge := by
  rw [strictDiagram_shape, ← Category.assoc, hornToCospanNerve_right_edge]
  apply SSet.yonedaEquiv.injective
  simp only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C).app (Opposite.op ⦋1⦌) _ =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ g)
  apply congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C).app _)
  refine ComposableArrows.ext₁ rfl rfl ?_
  change g = 𝟙 _ ≫ g ≫ 𝟙 _
  simp

/-- 通常の cospan の表示は、指定した二辺を貼った coherent 図式そのもの。 -/
lemma strictDiagram_eq :
    strictCospanHornIso.inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (AsSmall.down ⋙ cospan f g) =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).toTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g).toTruncated := by
  apply horn₂₂.isPushout.hom_ext
  · rw [strictDiagram_left, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeCospan_left]
    rfl
  · rw [strictDiagram_right, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeCospan_right]
    rfl

end SerrePositivity.KST.Spectra.CospanShape
