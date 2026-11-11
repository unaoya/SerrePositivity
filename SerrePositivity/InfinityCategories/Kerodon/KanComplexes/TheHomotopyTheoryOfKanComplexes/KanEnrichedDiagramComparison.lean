module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictDiagramPostcomposition

/-!
概要：Kan 値豊穣図式の比較と、豊穣関手による前合成。
方針：各添字の豊穣比較に添字の自然性を加え、全対象の図式の自然変換へ束ねる。
規約：全高次の Hom の自然性を比較のデータに保持する。
使われ方：底変換の切断比較を全添字と全対象で実現する。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 豊穣自然な比較を任意の豊穣関手で前合成する。 -/
def KanEnrichedComparison.precompose {C : Type v} {L : Type w}
    [Category.{u} C] [SimplicialCategory C] [Category.{u} L] [SimplicialCategory L]
    {F G : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}} (η : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison F G)
    (H : EnrichedFunctor SSet.{u} L C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison (H.comp SSet F) (H.comp SSet G) := by
  refine ⟨fun X ↦ η.val (H.obj X), ?_⟩
  intro X Y
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨x, θ⟩
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparison_app η (H.obj X) (H.obj Y) ((H.map X Y).app n θ) (𝟙 n) x

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison export _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedComparison (precompose)


/-- Kan 値豊穣図式を任意の豊穣関手で前合成する。 -/
def KanEnrichedDiagram.precompose {C : Type v} {L : Type w}
    [Category.{u} C] [SimplicialCategory C] [Category.{u} L] [SimplicialCategory L]
    {J : Type u} [Category.{u} J] (D : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram C J)
    (H : EnrichedFunctor SSet.{u} L C) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram L J where
  obj j := H.comp SSet (D.obj j)
  map f := (D.map f).precompose H
  map_id j X := D.map_id j (H.obj X)
  map_comp f g X := D.map_comp f g (H.obj X)

/-- 図式の前合成は図式値豊穣関手の前合成と厳密に一致する。 -/
lemma KanEnrichedDiagram.precompose_toEnrichedFunctor {C : Type v} {L : Type w}
    [Category.{u} C] [SimplicialCategory C] [Category.{u} L] [SimplicialCategory L]
    {J : Type u} [Category.{u} J] (D : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram C J)
    (H : EnrichedFunctor SSet.{u} L C) :
    (D.precompose H).toEnrichedFunctor = H.comp SSet D.toEnrichedFunctor := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro X Y
  simp only [eqToHom_refl, Category.comp_id]
  rfl

/-- 図式の前合成と coherent な共同実現は厳密に可換。 -/
lemma KanEnrichedDiagram.realization_precompose {C L : Type (u + 1)}
    [Category.{u} C] [SimplicialCategory C] [Category.{u} L] [SimplicialCategory L]
    {J : Type u} [Category.{u} J] (D : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram C J)
    (H : EnrichedFunctor SSet.{u} L C) :
    (D.precompose H).realization = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap H ≫ D.realization := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram.realization, precompose_toEnrichedFunctor, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp, Category.assoc]
  rfl

/-- 各添字の豊穣比較と添字方向の自然性を持つ二つの図式の比較。 -/
structure KanEnrichedDiagramComparison {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] (D E : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram C J) where
  component : ∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison (D.obj j) (E.obj j)
  naturality : ∀ {i j} (f : i ⟶ j) X,
    (D.map f).val X ≫ (component j).val X = (component i).val X ≫ (E.map f).val X

/-- 図式の豊穣比較は各対象で通常の図式の自然変換を与える。 -/
def KanEnrichedDiagramComparison.app {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] {D E : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram C J}
    (η : KanEnrichedDiagramComparison D E) (X : C) :
    D.evaluate X ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget ⟶ E.evaluate X ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget where
  app j := (η.component j).val X
  naturality _ _ f := η.naturality f X

/-- 図式の比較は全高次の Hom と添字の射の同時評価に対して自然。 -/
lemma KanEnrichedDiagramComparison.mixedNaturality
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] {D E : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram C J}
    (η : KanEnrichedDiagramComparison D E) (X Y : C)
    {i j : J} (f : i ⟶ j) {n k : SimplexCategoryᵒᵖ}
    (θ : (SimplicialCategory.sHom X Y).obj n) (α : n ⟶ k)
    (x : ((D.obj i).obj X).obj.obj k) :
    ((E.evaluate Y ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget).map f).app k
      ((((E.mappingSpaceMap X Y).app n θ).val i).app k α
        (((η.app X).app i).app k x)) =
    ((η.app Y).app j).app k
      (((D.evaluate Y ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget).map f).app k
        ((((D.mappingSpaceMap X Y).app n θ).val i).app k α x)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparison_app (η.component i) X Y θ α x
  change ((((E.mappingSpaceMap X Y).app n θ).val i).app k α
    (((η.app X).app i).app k x)) =
    ((η.app Y).app i).app k ((((D.mappingSpaceMap X Y).app n θ).val i).app k α x) at h
  rw [h]
  exact (congrArg (fun t ↦ t.app k
    ((((D.mappingSpaceMap X Y).app n θ).val i).app k α x)) ((η.app Y).naturality f)).symm

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
