module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.DiagramCommaSmallness
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallFibration
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitRestriction

/-!
概要：元の全図式 comma を小さい全空間と厳密な射影で表示する。
方針：実単体の小ささで縮小し、right fibration のホーン充填を宇宙から反映する。
規約：filtered 性と余極限性は未主張。使われ方：有限図式の単一 filtered 表示。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable (κ : Cardinal.{u}) {K C : SSet.{u}} [Quasicategory C]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C)

/-- 元の全図式 comma の小さい実模型。 -/
def smallDiagramComma : SSet.{u} := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallSimplicialSet.{u, u + 1} (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramComma κ D)

/-- 小さい模型の宇宙持ち上げと元の全 comma の実同型。 -/
def smallDiagramCommaIso :
    (SSet.uliftFunctor.{u + 1, u}).obj (smallDiagramComma κ D) ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramComma κ D :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallSimplicialSetIso.{u, u + 1} (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramComma κ D)

/-- 同じ元の小さい全図式圏への小さい射影。 -/
def smallDiagramCommaProjection : smallDiagramComma κ D ⟶ (ihom K).obj C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallSimplicialProjection.{u, u + 1} (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaProjection κ D)

/-- 同型と射影は元の全図式を厳密に保つ。 -/
lemma smallDiagramCommaIso_projection :
    (smallDiagramCommaIso κ D).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaProjection κ D =
      (SSet.uliftFunctor.{u + 1, u}).map (smallDiagramCommaProjection κ D) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallSimplicialProjection_ulift.{u, u + 1} (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaProjection κ D)).symm

instance smallDiagramCommaProjection_rightFibration :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration (smallDiagramCommaProjection κ D) := by
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration ((SSet.uliftFunctor.{u + 1, u}).map
      (smallDiagramCommaProjection κ D)) := by
    rw [← smallDiagramCommaIso_projection]
    exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightFibrations.comp_mem _ _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightFibrations.of_isIso (smallDiagramCommaIso κ D).hom) _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration.mem⟩
  constructor
  intro A B f hf
  cases hf with
  | @intro n i hi =>
    have : HasLiftingProperty (horn.{u + 1} (n + 1) i).ι
        ((SSet.uliftFunctor.{u + 1, u}).map (smallDiagramCommaProjection κ D)) :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration.mem _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightHornInclusions.intro i hi)
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.hasLiftingProperty_horn_of_ulift (smallDiagramCommaProjection κ D) n i

instance smallDiagramComma_quasicategory : Quasicategory (smallDiagramComma κ D) :=
  quasicategory_of_innerFibration (smallDiagramCommaProjection κ D)

/-- 小さい添字上でも同じ元の図式を頂点とする標準全余錐。 -/
def smallDiagramCommaCocone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone
    ((SSet.uliftFunctor.{u + 1, u}).map (smallDiagramCommaProjection κ D) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramYoneda κ K C) :=
  ⟨((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaCocone κ D).restrict (smallDiagramCommaIso κ D).hom).val, by
    rw [((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaCocone κ D).restrict (smallDiagramCommaIso κ D).hom).property,
      ← Category.assoc, smallDiagramCommaIso_projection]⟩

/-- 小さい標準全余錐の頂点は元の指定図式そのもの。 -/
lemma smallDiagramCommaCocone_vertex :
    (smallDiagramCommaCocone κ D).vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex D := by
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaCocone κ D).restrict (smallDiagramCommaIso κ D).hom).vertex = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_restrict, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaCocone_vertex]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
