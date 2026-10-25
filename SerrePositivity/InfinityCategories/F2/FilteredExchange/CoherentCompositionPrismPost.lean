module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentRightSlicePost
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCompositionLastPost

/-!
概要：元の合成 prism の全錐は、指定した同じ最終射の後合成に厳密に自然。
方針：元の各全単体を同じ豊穣座標で照合し、単体集合写像の外延性で束ねる。
規約：元の二 Hom 全体・時間・実 prism を保持。使われ方：Ncomp の二射合成の高次整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y Z W : C}

/-- 元の合成錐の豊穣座標は、元の全 Hom の合成単体そのもの。 -/
lemma coherentCompositionSliceSimplex_coordinate {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌)
    (τ : (SimplicialCategory.sHom Y Z) _⦋n⦌) (t : Fin (n + 1) →o Fin 2) :
    coherentRightSliceSimplex Z (coherentCompositionSliceSimplex σ τ t) =
      coherentCompositionSimplex σ τ t := by
  simp only [coherentRightSliceSimplex, coherentCompositionSliceSimplex,
    Category.assoc, Iso.inv_hom_id_assoc, Equiv.apply_symm_apply]

/-- 元の合成錐の各全単体の指定後合成は、同じ第二 Hom の指定後合成に厳密に一致する。 -/
lemma coherentCompositionSliceSimplex_post {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌)
    (τ : (SimplicialCategory.sHom Y Z) _⦋n⦌) (g : Z ⟶ W) (t : Fin (n + 1) →o Fin 2) :
    coherentRightSlicePostSimplex g (coherentCompositionSliceSimplex σ τ t) =
      coherentCompositionSliceSimplex σ ((eHomWhiskerLeft SSet Y g).app (Opposite.op ⦋n⦌) τ) t := by
  apply coherentRightSliceSimplex_injective W
  rw [coherentRightSlicePostSimplex_coordinate,
    coherentCompositionSliceSimplex_coordinate σ
      ((eHomWhiskerLeft SSet Y g).app (Opposite.op ⦋n⦌) τ) t]
  have e := coherentSimplexLastPost_of_source_eq
    (coherentCompositionSliceSimplex_coordinate σ τ t)
    (coherentRightSliceSimplex_last Z (coherentCompositionSliceSimplex σ τ t))
    (coherentCompositionObj_last X Y Z n t) g
  exact e.trans (coherentCompositionSimplex_last_post σ τ g t)

/-- 元の同じ全パラメータ合成 prism の指定後合成は、第二 Hom の後合成の実際の制限。 -/
lemma coherentCompositionPrism_post (g : Z ⟶ W) :
    coherentCompositionPrism X Y Z ≫ coherentRightSlicePost g =
      (Δ[1] ◁ (𝟙 ((SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y)) ⊗ₘ
        (SSet.uliftFunctor.{v, u}).map (eHomWhiskerLeft SSet Y g))) ≫
          coherentCompositionPrism X Y W := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, ⟨σ⟩, ⟨τ⟩⟩
  change coherentRightSlicePostSimplex g
    (coherentCompositionSliceSimplex σ τ (stdSimplex.objEquiv t).toOrderHom) =
      coherentCompositionSliceSimplex σ ((eHomWhiskerLeft SSet Y g).app (Opposite.op ⦋n⦌) τ)
        (stdSimplex.objEquiv t).toOrderHom
  exact coherentCompositionSliceSimplex_post σ τ g _

end SerrePositivity.InfinityCategories.F2
