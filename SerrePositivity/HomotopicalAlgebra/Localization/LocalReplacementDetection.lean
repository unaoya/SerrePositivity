module

public import SerrePositivity.HomotopicalAlgebra.Localization.Detection

/-! # Local equivalences detected by a local replacement with local unit

A local equivalence between local objects is an original weak equivalence.
Consequently a functor into local objects whose unit is a local equivalence
identifies W_S with the inverse image of the original W. The local-unit
hypothesis is explicit; constructing it remains a separate task.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.Bousfield
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

include hcof hfib in
lemma weakEquivalence_of_mappingTests_at_ends {X Y : C} (f : X ⟶ Y)
    (hX : mappingTest cof fib X f) (hY : mappingTest cof fib Y f) : weakEquivalences C f := by
  let L := (weakEquivalences C).Q
  have hpre (Z : C) (hZ : mappingTest cof fib Z f) :
      Function.Bijective (fun k : L.obj Y ⟶ L.obj Z => L.map f ≫ k) := by
    have := chosenMappingSpace_isFibrant cof fib hfib (Opposite.op X) Z
    have := chosenMappingSpace_isFibrant cof fib hfib (Opposite.op Y) Z
    have : WeakEquivalence (((chosenResolutionHom cof fib).map f.op).app Z) := ⟨hZ⟩
    have hb := SimplicialModel.piZero_bijective_of_weakEquivalence_of_fibrant hcof
      (((chosenResolutionHom cof fib).map f.op).app Z)
    let eX := chosenResolutionHomPiZeroEquiv L cof fib (Opposite.op X) Z
    let eY := chosenResolutionHomPiZeroEquiv L cof fib (Opposite.op Y) Z
    have hnat (z) : eX (SSet.mapπ₀ (((chosenResolutionHom cof fib).map f.op).app Z) z) =
        L.map f ≫ eY z := chosenResolutionHomPiZeroEquiv_naturality_source L cof fib f.op Z z
    have hb' := eX.bijective.comp (hb.comp eY.symm.bijective)
    simpa only [Function.comp_def, hnat, Equiv.apply_symm_apply] using hb'
  obtain ⟨g, hg⟩ := (hpre X hX).surjective (𝟙 (L.obj X))
  have hg' : g ≫ L.map f = 𝟙 (L.obj Y) := (hpre Y hY).injective (by
    simp only [← Category.assoc, hg, Category.id_comp, Category.comp_id])
  have : IsIso (L.map f) := ⟨g, hg, hg'⟩
  exact (Quillen.weakEquivalences_iff_isIso_map L f).mpr inferInstance

include hcof hfib in
lemma localEquivalence_iff_weakEquivalence_between_localObjects
    (S : MorphismProperty C) {X Y : C} (f : X ⟶ Y)
    (hX : localObjects cof fib S X) (hY : localObjects cof fib S Y) :
    localEquivalences cof fib S f ↔ weakEquivalences C f := by
  constructor
  · intro hf
    exact weakEquivalence_of_mappingTests_at_ends cof fib hcof hfib f (hf X hX) (hf Y hY)
  · exact weakEquivalences_le_localEquivalences cof fib hcof S f

include hcof hfib in
lemma localEquivalences_eq_inverseImage_of_localUnit (S : MorphismProperty C)
    (R : C ⥤ C) (η : 𝟭 C ⟶ R)
    (hR : ∀ X, localObjects cof fib S (R.obj X))
    (hη : ∀ X, localEquivalences cof fib S (η.app X)) :
    localEquivalences cof fib S = (weakEquivalences C).inverseImage R := by
  ext X Y f
  have he : localEquivalences cof fib S (R.map f) ↔ localEquivalences cof fib S f := by
    have hn : f ≫ η.app Y = η.app X ≫ R.map f := η.naturality f
    constructor
    · intro hf
      exact (localEquivalences cof fib S).of_postcomp _ _ (hη Y)
        (hn.symm ▸ (localEquivalences cof fib S).comp_mem _ _ (hη X) hf)
    · intro hf
      exact (localEquivalences cof fib S).of_precomp _ _ (hη X)
        (hn ▸ (localEquivalences cof fib S).comp_mem _ _ hf (hη Y))
  exact he.symm.trans (localEquivalence_iff_weakEquivalence_between_localObjects
    cof fib hcof hfib S (R.map f) (hR X) (hR Y))

end SerrePositivity.Bousfield
