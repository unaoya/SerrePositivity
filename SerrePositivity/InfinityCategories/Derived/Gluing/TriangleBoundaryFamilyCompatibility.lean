module
public import SerrePositivity.InfinityCategories.F1B.TriangleBoundaryGluing

/-! パラメーター付き三角形境界の二枝は、同じ対角の両端で貼り合う。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
variable {T X : SSet.{u}}

lemma dgGluingTriangleEndpointsFamily_hom_ext
    {f g : (triangleDiagonalEndpoints : SSet.{u}) ⊗ T ⟶ X}
    (h₀ : (triangleDiagonalEndpointZero ▷ T) ≫ f = (triangleDiagonalEndpointZero ▷ T) ≫ g)
    (h₂ : (triangleDiagonalEndpointTwo ▷ T) ≫ f = (triangleDiagonalEndpointTwo ▷ T) ≫ g) :
    f = g := by
  apply (triangleDiagonalEndpoints_bicartSq.isPushout.map (tensorRight T)).hom_ext
  · apply (cancel_epi ((stdSimplex.faceSingletonIso (0 : Fin 3)).hom ▷ T)).mp
    simpa only [triangleDiagonalEndpointZero, comp_whiskerRight, tensorRight, Functor.flip,
      curriedTensor, Category.assoc] using h₀
  · apply (cancel_epi ((stdSimplex.faceSingletonIso (2 : Fin 3)).hom ▷ T)).mp
    simpa only [triangleDiagonalEndpointTwo, comp_whiskerRight, tensorRight, Functor.flip,
      curriedTensor, Category.assoc] using h₂

lemma dgGluingTriangleBoundaryFamily_compatible
    (a : (horn 2 1 : SSet.{u}) ⊗ T ⟶ X) (b : (Δ[1] : SSet.{u}) ⊗ T ⟶ X)
    (h₀ : (stdSimplex.δ (1 : Fin 2) ▷ T) ≫ b =
      (stdSimplex.δ (1 : Fin 2) ▷ T) ≫ (horn₂₁.ι₀₁ ▷ T) ≫ a)
    (h₂ : (stdSimplex.δ (0 : Fin 2) ▷ T) ≫ b =
      (stdSimplex.δ (0 : Fin 2) ▷ T) ≫ (horn₂₁.ι₁₂ ▷ T) ≫ a) :
    (Subcomplex.homOfLE triangleBoundary_bicartSq.le₁₂ ▷ T) ≫ a =
      (Subcomplex.homOfLE triangleBoundary_bicartSq.le₁₃ ▷ T) ≫
        (triangleDiagonalFaceIso.inv ▷ T) ≫ b := by
  apply dgGluingTriangleEndpointsFamily_hom_ext
  · have hh := congrArg (tensorRight T).map triangleDiagonalEndpointZero_horn
    have hd := congrArg (tensorRight T).map triangleDiagonalEndpointZero_diagonal
    simp only [Functor.map_comp, tensorRight, Functor.flip, curriedTensor] at hh hd
    refine (show _ = (stdSimplex.δ (1 : Fin 2) ▷ T) ≫ (horn₂₁.ι₀₁ ▷ T) ≫ a by
      simpa only [Category.assoc] using congrArg (fun k => k ≫ a) hh).trans ?_
    refine h₀.symm.trans ?_
    simpa only [comp_whiskerRight, Category.assoc] using congrArg (fun k => k ≫ b) hd.symm
  · have hh := congrArg (tensorRight T).map triangleDiagonalEndpointTwo_horn
    have hd := congrArg (tensorRight T).map triangleDiagonalEndpointTwo_diagonal
    simp only [Functor.map_comp, tensorRight, Functor.flip, curriedTensor] at hh hd
    refine (show _ = (stdSimplex.δ (0 : Fin 2) ▷ T) ≫ (horn₂₁.ι₁₂ ▷ T) ≫ a by
      simpa only [Category.assoc] using congrArg (fun k => k ≫ a) hh).trans ?_
    refine h₂.symm.trans ?_
    simpa only [comp_whiskerRight, Category.assoc] using congrArg (fun k => k ≫ b) hd.symm

end SerrePositivity.InfinityCategories
