module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.RightClassifiedIndDensityCocone
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.WeightedTotalAssemblyCofinal
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalCoconeRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.CofinalUniverseLift

/-!
概要：strict 図式の元の weighted 全空間上で、同じ分類余極限を頂点とする Indκ 密度余錐。
方針：元の全空間の密度余錐を、証明済みの同じ right cofinal 比較で制限する。
規約：元の底への射影と全余錐を保持。使われ方：各段の密度余極限との Kan 合成。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

variable (κ : Cardinal.{u}) [Fact κ.IsRegular] {C : SSet.{u}} [Quasicategory C]
  {I : Type u} [PartialOrder I] [IsFiltered I] [IsCardinalFiltered I κ]
  (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject C) [∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ (F.obj i).val.left]

local instance : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictRightFibrationColimit F).val.left :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictRightFibrationColimit_isKappaFiltered F

/-- 元の weighted 全空間から、同じ各段の射影で定める元の底への射。 -/
def weightedIndDensityBase : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationTotalDiagram F) ⟶ C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationProjectionCocone F).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveConstantEvaluation I C

/-- 元の weighted 全空間上の、同じ元の射影による表現可能図式。 -/
def weightedIndDensityDiagram :
    (SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationTotalDiagram F)) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C :=
  (SSet.uliftFunctor.{u + 1, u}).map (weightedIndDensityBase F) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C

omit [Fact κ.IsRegular] [IsCardinalFiltered I κ] [∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ (F.obj i).val.left] in
/-- 元の全空間比較による密度図式の制限は、元の weighted 底射影を厳密に回収する。 -/
lemma weightedIndDensity_diagram :
    (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictRightFibrationTotalAssembly F) ≫
      ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictRightFibrationColimitProjection F) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C) =
        weightedIndDensityDiagram κ F := by
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictRightFibrationTotalAssembly_projection]
  rfl

/-- 元の weighted 全空間を添字とする、同じ分類余極限の全密度余錐。 -/
def weightedIndDensityCocone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (weightedIndDensityDiagram κ F) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq (weightedIndDensity_diagram κ F)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightClassifiedIndDensityCocone κ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictRightFibrationColimit F)).restrict
      ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictRightFibrationTotalAssembly F)))

/-- 同じ全密度余錐の頂点は、元の全空間余極限の元の分類値。 -/
lemma weightedIndDensityCocone_vertex :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indInclusionPresheaf κ C).app (Opposite.op ⦋0⦌) (weightedIndDensityCocone κ F).vertex =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightStraighteningPresheafDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictRightFibrationColimit F)) := by
  rw [weightedIndDensityCocone, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_restrict]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightClassifiedIndDensityCocone_vertex κ _

/-- 元の weighted 全空間上の同じ全密度余錐は native な余極限。 -/
lemma weightedIndDensityCocone_isColimit : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (weightedIndDensityCocone κ F) := by
  have : Quasicategory (CategoryTheory.Limits.colimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationTotalDiagram F)) :=
    quasicategory_of_innerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictRightFibrationColimitProjection F)
  apply (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq_isColimit_iff _ _).mp
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isColimitCone_iff_restrict_rightCofinal _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isRightCofinal_ulift _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictRightFibrationTotalAssembly_isRightCofinal (κ := κ) F)) _).mp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightClassifiedIndDensityCocone_isColimit κ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictRightFibrationColimit F))

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
