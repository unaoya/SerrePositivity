module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallFullSubcomplex
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.UniverseHorns
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FullSubcomplexMapping

/-!
概要：小さい頂点族上の全部分圏を宇宙 u の ∞ 圏で厳密に模型化する。
方針：全次数の縮小同型を使い、持ち上げたホーン充填から quasicategory 性を反映する。
規約：元の大きい標的への包含を保持し、その充満忠実性を実証する。
使われ方：Ind 内の共通の小さい μ-compact 族から小さい生成圏を得る。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 全 inner horn の持ち上げと降下により、元の宇宙の quasicategory 性を反映する。 -/
lemma quasicategory_of_ulift (X : SSet.{u})
    [Quasicategory ((SSet.uliftFunctor.{v, u}).obj X)] : Quasicategory X := by
  constructor
  intro n i f h0 hn
  obtain ⟨g, hg⟩ := Quasicategory.hornFilling h0 hn
    ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftHornIso.{u, v} (n + 2) i).inv ≫ (SSet.uliftFunctor.{v, u}).map f)
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftMorphismDown ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, v} (n + 2)).hom ≫ g), ?_⟩
  apply (SSet.uliftFunctor.{v, u}).map_injective
  rw [Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftMorphismDown_lift, ← Category.assoc,
    ← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftHornIso_ι, Category.assoc, ← hg, Iso.hom_inv_id_assoc]

variable {X : SSet.{u + 1}} (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasSmallFixedVertexMaps X)
  {T : Type u} (v : T → X _⦋0⦌)

/-- 共通の小さい族の値上の全部分圏を、元の小さい宇宙で縮小する。 -/
def smallFullModel : SSet.{u} := by
  have (n : SimplexCategoryᵒᵖ) := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.small_fullSubcomplexOnRange hX v n
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallSimplicialSet.{u, u + 1}
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X (fun x ↦ x ∈ Set.range v)).toSSet

/-- 縮小模型の持ち上げと、元の全部分圏の全単体の同型。 -/
def smallFullModelIso : (SSet.uliftFunctor.{u + 1, u}).obj (smallFullModel hX v) ≅
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X (fun x ↦ x ∈ Set.range v)).toSSet :=
  by
    have (n : SimplexCategoryᵒᵖ) := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.small_fullSubcomplexOnRange hX v n
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallSimplicialSetIso.{u, u + 1} _

instance smallFullModel_quasicategory [Quasicategory X] : Quasicategory (smallFullModel hX v) := by
  have : InnerFibration (smallFullModelIso hX v).hom :=
    ⟨MorphismProperty.of_isIso innerFibrations _⟩
  have := quasicategory_of_innerFibration (smallFullModelIso hX v).hom
  exact quasicategory_of_ulift.{u, u + 1} (smallFullModel hX v)

/-- 小さい模型から元の大きい標的への、同じ全部分包含。 -/
def smallFullModelInclusion : (SSet.uliftFunctor.{u + 1, u}).obj (smallFullModel hX v) ⟶ X :=
  (smallFullModelIso hX v).hom ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X (fun x ↦ x ∈ Set.range v)).ι

/-- 元の全部分包含と縮小同型の合成は、全写像空間で充満忠実。 -/
lemma smallFullModelInclusion_isFullyFaithful [Quasicategory X] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (smallFullModelInclusion hX v) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (smallFullModelIso hX v)).isFullyFaithful.comp
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι _ _)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
