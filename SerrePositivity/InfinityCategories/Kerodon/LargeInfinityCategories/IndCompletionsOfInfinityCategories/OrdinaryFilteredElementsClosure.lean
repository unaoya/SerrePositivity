module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.PresheafDiagramStrictification
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ClassifiedFilteredElements
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.KanDiagramColimitTransport

/-!
概要：通常の κ-filtered 添字上の任意の coherent 前層図式で、元の圏の κ-filtered 性は余極限で保たれる。
方針：元の図式の大域 strict 化で頂点を保つ余極限余錐を輸送し、同じ分類図式の保存を使う。
規約：元の coherent 図式や native 余錐に strict 性を仮定しない。
使われ方：一般の小さい κ-filtered 添字の cofinal poset への制限。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

variable {C : SSet.{u}} [Quasicategory C]

/-- 元の coherent 図式の各値の条件を、同じ大域 strict 化の実際の分類値へ移す。 -/
lemma hasKappaFilteredElements_strictification_values {κ : Cardinal.{u}}
    {I : Type u} [Category.{u} I]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C)
    (hF : ∀ i : (nerve I) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasKappaFilteredElements κ (F.app (Opposite.op ⦋0⦌) (ULift.up i))) (i : I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasKappaFilteredElements κ ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.rightStraighteningInfinityMap C).app _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.presheafDiagramRightStrict F).obj i))) := by
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.presheafDiagramRightStrictClassificationIso F).app (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i))
  have hv := congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.rightStraighteningInfinityMap C).app (Opposite.op ⦋0⦌))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.presheafDiagramRightStrict F) i)
  have e := (eqToIso (congrArg HomotopyCategory.mk hv)).symm ≪≫ h
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.hasKappaFilteredElements_isoClosed κ C e.symm (hF (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i))

/-- 同じ通常の κ-filtered 添字上の任意の native 前層余極限で、元の圏は κ-filtered。 -/
lemma hasKappaFilteredElements_of_ordinary_colimit
    {κ : Cardinal.{u}} [Fact κ.IsRegular] {I : Type u} [SmallCategory I]
    [IsCardinalFiltered I κ]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
    (hF : ∀ i : (nerve I) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasKappaFilteredElements κ (F.app (Opposite.op ⦋0⦌) (ULift.up i))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasKappaFilteredElements κ c.vertex := by
  obtain ⟨d, hd, hv⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.exists_colimitCocone_functorIso_sameVertex
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.presheafDiagramRightStrictClassificationIso F).symm c hc
  rw [← hv]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.hasKappaFilteredElements_of_strictClassified_colimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.presheafDiagramRightStrict F)
    (hasKappaFilteredElements_strictification_values F hF) d hd

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
