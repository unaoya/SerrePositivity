module

public import SerrePositivity.InfinityCategories.F1.KanDiagramNaturalTransformation
public import SerrePositivity.InfinityCategories.F1.CoherentOrderPostcomposition

/-!
概要：元の通常の Kan 図式と自然変換を、同じ KanDiagramObject の通常の図式に束縛する。
方針：既存の kanDiagramHom の恒等・合成則を豊穣 Hom の頂点で検証する。
規約：図式の全変換空間の Kan 性を要求しない。
使われ方：元の filtered 余極限余錐全体を関手空間へ実現する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
variable {I : Type u} [SmallCategory I]

/-- 元の自然変換を束縛した射の豊穣頂点は、元の全成分の頂点そのもの。 -/
lemma kanDiagramHom_vertex {F G : KanDiagramObject I}
    (η : F.val ⋙ kanObjectForget ⟶ G.val ⋙ kanObjectForget) :
    SimplicialCategory.homEquiv' F G (kanDiagramHom η) = strictDiagramMappingVertex η := by
  change (SSet.unitHomEquiv _) ((SSet.unitHomEquiv _).symm _) = _
  exact Equiv.apply_symm_apply _ _

/-- 元の恒等変換の束縛は、同じ束縛対象の恒等射。 -/
lemma kanDiagramHom_id (F : KanDiagramObject I) :
    kanDiagramHom (𝟙 (F.val ⋙ kanObjectForget)) = 𝟙 F := by
  apply (SimplicialCategory.homEquiv' F F).injective
  rw [kanDiagramHom_vertex]
  change _ = (SSet.unitHomEquiv _) (eId SSet.{u} F)
  rfl

/-- 元の自然変換の合成は、束縛された通常の射の合成を厳密に保つ。 -/
lemma kanDiagramHom_comp {F G H : KanDiagramObject I}
    (η : F.val ⋙ kanObjectForget ⟶ G.val ⋙ kanObjectForget)
    (θ : G.val ⋙ kanObjectForget ⟶ H.val ⋙ kanObjectForget) :
    kanDiagramHom (η ≫ θ) = kanDiagramHom η ≫ kanDiagramHom θ := by
  apply (SimplicialCategory.homEquiv' F H).injective
  rw [kanDiagramHom_vertex]
  change _ = (SSet.unitHomEquiv _) (eHomEquiv SSet (kanDiagramHom η ≫ kanDiagramHom θ))
  rw [eHomEquiv_comp]
  apply Subtype.ext
  funext i
  apply CategoryTheory.Functor.functorHom_ext
  intro n α
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 元の全 Kan 図式と全自然変換を束縛する通常の関手。 -/
def kanDiagramBundle : (I ⥤ KanObject.{u}) ⥤ KanDiagramObject I where
  obj F := ⟨F, trivial⟩
  map η := kanDiagramHom (Functor.whiskerRight η kanObjectForget)
  map_id F := by
    erw [Functor.whiskerRight_id]
    exact kanDiagramHom_id (⟨F, trivial⟩ : KanDiagramObject I)
  map_comp {F G H} η θ := by
    erw [Functor.whiskerRight_comp]
    exact kanDiagramHom_comp (F := ⟨F, trivial⟩) (G := ⟨G, trivial⟩) (H := ⟨H, trivial⟩) _ _

/-- 束縛された射の豊穣評価は、元の指定成分の射そのもの。 -/
lemma kanDiagramHom_evaluation {F G : KanDiagramObject I}
    (η : F.val ⋙ kanObjectForget ⟶ G.val ⋙ kanObjectForget) (i : I) :
    (coherentEnrichedUnderlyingFunctor (kanDiagramEvaluationEnriched i)).map
      (kanDiagramHom η) = η.app i := by
  apply (SimplicialCategory.homEquiv' (F.val.obj i) (G.val.obj i)).injective
  have h := coherentEnrichedUnderlyingFunctor_vertex (kanDiagramEvaluationEnriched i)
    (X := F) (Y := G) (kanDiagramHom η)
  rw [kanDiagramHom_vertex] at h
  exact h

/-- 束縛後の評価関手は、元の通常の評価関手と一致する。 -/
lemma kanDiagramBundle_evaluation (i : I) :
    kanDiagramBundle ⋙ coherentEnrichedUnderlyingFunctor (kanDiagramEvaluationEnriched i) =
      (evaluation I KanObject.{u}).obj i := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro F G η
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact kanDiagramHom_evaluation _ i

end SerrePositivity.InfinityCategories.F2.Presentable
