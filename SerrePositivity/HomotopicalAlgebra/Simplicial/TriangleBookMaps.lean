module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.TriangleBook

/-! # Strict reindexing of triangles with a shared edge -/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.TriangleBook

lemma hom_ext {I : Type v} {Q : SSet.{v}} {f g : obj I ⟶ Q}
    (h : ∀ i, triangle I i ≫ f = triangle I i ≫ g)
    (hd : sharedEdge I ≫ f = sharedEdge I ≫ g) : f = g := by
  apply pushout.hom_ext
  · apply Sigma.hom_ext
    intro i
    exact (Category.assoc _ _ _).symm.trans ((h i).trans (Category.assoc _ _ _))
  · exact hd

def reindex {I J : Type v} (α : I → J) : obj I ⟶ obj J :=
  desc (sharedEdge J) (fun i => triangle J (α i)) (fun i => triangle_sharedEdge J (α i))

@[reassoc (attr := simp)]
lemma triangle_reindex {I J : Type v} (α : I → J) (i : I) :
    triangle I i ≫ reindex α = triangle J (α i) := triangle_desc _ _ _ i

@[reassoc (attr := simp)]
lemma sharedEdge_reindex {I J : Type v} (α : I → J) :
    sharedEdge I ≫ reindex α = sharedEdge J := sharedEdge_desc _ _ _

lemma reindex_id (I : Type v) : reindex (id : I → I) = 𝟙 (obj I) := by
  apply hom_ext
  · intro i
    exact (triangle_reindex id i).trans (Category.comp_id _).symm
  · exact (sharedEdge_reindex id).trans (Category.comp_id _).symm

lemma reindex_comp {I J K : Type v} (α : I → J) (β : J → K) :
    reindex α ≫ reindex β = reindex (β ∘ α) := by
  apply hom_ext
  · intro i
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ reindex β) (triangle_reindex α i)).trans
        ((triangle_reindex β (α i)).trans (triangle_reindex (β ∘ α) i).symm))
  · exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ reindex β) (sharedEdge_reindex α)).trans
        ((sharedEdge_reindex β).trans (sharedEdge_reindex (β ∘ α)).symm))

lemma desc_reindex {I J : Type v} {Q : SSet.{v}} (α : I → J)
    (d : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ Q)
    (f : J → (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 2) ⟶ Q))
    (hf : ∀ j, SSet.stdSimplex.δ (1 : Fin 3) ≫ f j = d) :
    reindex α ≫ desc d f hf = desc d (fun i => f (α i)) (fun i => hf (α i)) := by
  apply hom_ext
  · intro i
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ desc d f hf) (triangle_reindex α i)).trans
        ((triangle_desc d f hf (α i)).trans
          (triangle_desc d (fun i => f (α i)) (fun i => hf (α i)) i).symm))
  · exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ desc d f hf) (sharedEdge_reindex α)).trans
        ((sharedEdge_desc d f hf).trans
          (sharedEdge_desc d (fun i => f (α i)) (fun i => hf (α i))).symm))

end SerrePositivity.SimplicialModel.TriangleBook
