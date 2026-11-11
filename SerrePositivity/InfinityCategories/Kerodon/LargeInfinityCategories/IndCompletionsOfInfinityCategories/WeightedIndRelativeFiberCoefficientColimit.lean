module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.WeightedIndRelativeFiberTransformation

/-!
概要：元の相対 join の実際の fiber 余錐と左 Kan 像は、係数同型で戻したまま余極限。
方針：同じ標準変換の厳密な同定と、同じ係数単位から実現した余錐の全比較を使う。
規約：実際の fiber 余錐を選び直さない。使われ方：元の全図式の全 fiber 局所普遍性。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
  {I : Type u} [PartialOrder I] (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject C)
  (hF : ∀ v, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IsIndVertex κ C
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.rightStraighteningInfinityMap C).app
      (Opposite.op ⦋0⦌) v)) (i : I)

/-- 実際の相対 join fiber 余錐を同じ係数全空間へ戻した余錐は、元の係数図式の余極限。 -/
lemma weightedIndRelativeFiberCoefficientCocone_isColimit :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedIndRelativeFiberCoefficientCocone κ F hF i) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isColimitCone_of_coconeTransformationIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedIndRelativeCoefficientCocone κ F hF i) _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedIndCoefficientVertex κ F hF i)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedIndRelativeCoefficientCocone_vertex κ F hF i)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedIndRelativeFiberCoefficientCocone_vertex κ F hF i) _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedIndRelativeCoefficientCocone_isColimit κ F hF i)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.homotopyCoconeTransformationIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedIndRelativeCoefficientHomotopy κ F hF i)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedIndRelativeCoefficientRealization κ F hF i) ≪≫
      eqToIso (congrArg HomotopyCategory.mk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedIndRelativeFiberCoefficientTransformationVertex_eq κ F hF i).symm)

/-- 同じ実際の fiber 余錐を係数へ戻したまま、元の左 Kan 延長の像も余極限となる。 -/
lemma weightedIndRelativeFiberCoefficientCocone_image_isColimit
    [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ (F.obj i).val.left] {E : SSet.{u + 1}} [Quasicategory E]
    {F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ E} {G : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C ⟶ E}
    (β : SSet.Homotopy F₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C ≫ G))
    (hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C) F₀ G β) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone G (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedIndRelativeFiberCoefficientCocone κ F hF i)) := by
  let c := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedIndRelativeCoefficientCocone κ F hF i
  let d := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedIndRelativeFiberCoefficientCocone κ F hF i
  have hGc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone G c) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedIndRelativeCoefficientCocone_image_isColimit κ F hF i β hβ
  exact hGc.of_functorIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeFunctorIsoOfVertexIso c d (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitConeIso c d
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedIndRelativeCoefficientCocone_isColimit κ F hF i)
    (weightedIndRelativeFiberCoefficientCocone_isColimit κ F hF i))).postcomp G)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
