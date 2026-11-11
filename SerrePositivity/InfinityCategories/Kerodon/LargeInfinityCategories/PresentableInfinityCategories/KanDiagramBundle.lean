module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramNaturalTransformation
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.OrderPostcomposition

/-!
概要：元の通常の Kan 図式と自然変換を、同じ KanDiagramObject の通常の図式に束縛する。
方針：既存の kanDiagramHom の恒等・合成則を豊穣 Hom の頂点で検証する。
規約：図式の全変換空間の Kan 性を要求しない。
使われ方：元の filtered 余極限余錐全体を関手空間へ実現する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable {I : Type u} [SmallCategory I]

/-- 元の自然変換を束縛した射の豊穣頂点は、元の全成分の頂点そのもの。 -/
lemma kanDiagramHom_vertex {F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I}
    (η : F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget ⟶ G.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) :
    SimplicialCategory.homEquiv' F G (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramHom η) = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingVertex η := by
  change (SSet.unitHomEquiv _) ((SSet.unitHomEquiv _).symm _) = _
  exact Equiv.apply_symm_apply _ _

/-- 元の恒等変換の束縛は、同じ束縛対象の恒等射。 -/
lemma kanDiagramHom_id (F : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramHom (𝟙 (F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)) = 𝟙 F := by
  apply (SimplicialCategory.homEquiv' F F).injective
  rw [kanDiagramHom_vertex]
  change _ = (SSet.unitHomEquiv _) (eId SSet.{u} F)
  rfl

/-- 元の自然変換の合成は、束縛された通常の射の合成を厳密に保つ。 -/
lemma kanDiagramHom_comp {F G H : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I}
    (η : F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget ⟶ G.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)
    (θ : G.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget ⟶ H.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramHom (η ≫ θ) = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramHom η ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramHom θ := by
  apply (SimplicialCategory.homEquiv' F H).injective
  rw [kanDiagramHom_vertex]
  change _ = (SSet.unitHomEquiv _) (eHomEquiv SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramHom η ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramHom θ))
  rw [eHomEquiv_comp]
  apply Subtype.ext
  funext i
  apply CategoryTheory.Functor.functorHom_ext
  intro n α
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 元の全 Kan 図式と全自然変換を束縛する通常の関手。 -/
def kanDiagramBundle : (I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I where
  obj F := ⟨F, trivial⟩
  map η := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramHom (Functor.whiskerRight η _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)
  map_id F := by
    erw [Functor.whiskerRight_id]
    exact kanDiagramHom_id (⟨F, trivial⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I)
  map_comp {F G H} η θ := by
    erw [Functor.whiskerRight_comp]
    exact kanDiagramHom_comp (F := ⟨F, trivial⟩) (G := ⟨G, trivial⟩) (H := ⟨H, trivial⟩) _ _

/-- 束縛された射の豊穣評価は、元の指定成分の射そのもの。 -/
lemma kanDiagramHom_evaluation {F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I}
    (η : F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget ⟶ G.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) (i : I) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramEvaluationEnriched i)).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramHom η) = η.app i := by
  apply (SimplicialCategory.homEquiv' (F.val.obj i) (G.val.obj i)).injective
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor_vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramEvaluationEnriched i)
    (X := F) (Y := G) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramHom η)
  rw [kanDiagramHom_vertex] at h
  exact h

/-- 束縛後の評価関手は、元の通常の評価関手と一致する。 -/
lemma kanDiagramBundle_evaluation (i : I) :
    kanDiagramBundle ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramEvaluationEnriched i) =
      (evaluation I _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}).obj i := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro F G η
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact kanDiagramHom_evaluation _ i

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
