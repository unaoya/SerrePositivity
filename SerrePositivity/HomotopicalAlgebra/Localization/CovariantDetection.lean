module

public import SerrePositivity.HomotopicalAlgebra.Localization.Detection
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SmallHomComparison

/-! # Detecting original weak equivalences by covariant RMap tests

The π₀ comparison converts every-source tests to postcomposition on the
ordinary homotopy category. Actual inverses are obtained by Yoneda and
reflected back by the proved model-category saturation theorem.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.Bousfield
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [ModelCategory SSet.{v}]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

include hcof hfib in
lemma weakEquivalence_of_covariant_mappingTests {X Y : C} (f : X ⟶ Y)
    (hf : ∀ Z, weakEquivalences SSet.{v}
      (((chosenResolutionHom cof fib).obj (Opposite.op Z)).map f)) : weakEquivalences C f := by
  let L := (weakEquivalences C).Q
  have hpost (Z : C) : Function.Bijective
      (fun k : L.obj Z ⟶ L.obj X => k ≫ L.map f) := by
    have := chosenMappingSpace_isFibrant cof fib hfib (Opposite.op Z) X
    have := chosenMappingSpace_isFibrant cof fib hfib (Opposite.op Z) Y
    have : WeakEquivalence (((chosenResolutionHom cof fib).obj (Opposite.op Z)).map f) := ⟨hf Z⟩
    have hb := SimplicialModel.piZero_bijective_of_weakEquivalence_of_fibrant hcof
      (((chosenResolutionHom cof fib).obj (Opposite.op Z)).map f)
    let eX := chosenResolutionHomPiZeroEquiv L cof fib (Opposite.op Z) X
    let eY := chosenResolutionHomPiZeroEquiv L cof fib (Opposite.op Z) Y
    have hnat (z) : eY (SSet.mapπ₀ (((chosenResolutionHom cof fib).obj (Opposite.op Z)).map f) z) =
        eX z ≫ L.map f := chosenResolutionHomPiZeroEquiv_naturality_target L cof fib
          (Opposite.op Z) f z
    have hb' := eY.bijective.comp (hb.comp eX.symm.bijective)
    simpa only [Function.comp_def, hnat, Equiv.apply_symm_apply] using hb'
  obtain ⟨g, hg⟩ := (hpost Y).surjective (𝟙 (L.obj Y))
  have hg' : L.map f ≫ g = 𝟙 (L.obj X) := (hpost X).injective (by
    simp only [Category.assoc, hg, Category.id_comp, Category.comp_id])
  have : IsIso (L.map f) := ⟨g, hg', hg⟩
  exact (Quillen.weakEquivalences_iff_isIso_map L f).mpr inferInstance

end SerrePositivity.Bousfield

namespace SerrePositivity.HomotopyFunctionComplex.SmallHomComparison
variable {C : Type u} [Category.{v} C] [ModelCategory C] [IsLocallyPresentable.{w} C]

def targetArrowIso (Q : C ⥤ SimplexCategory ⥤ C) (R : C ⥤ C)
    (X : Cᵒᵖ) {Y Z : C} (f : Y ⟶ Z) :
    Arrow.mk (SSet.uliftFunctor.{v,w}.map (((hom Q R).obj X).map f)) ≅
      Arrow.mk (SSet.uliftFunctor.{w,v}.map (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.resolutionHom Q R).obj X).map f)) :=
  Arrow.isoMk (((resolutionLiftIso Q R).app X).app Y) (((resolutionLiftIso Q R).app X).app Z)
    (((resolutionLiftIso Q R).app X).hom.naturality f).symm

end SerrePositivity.HomotopyFunctionComplex.SmallHomComparison
