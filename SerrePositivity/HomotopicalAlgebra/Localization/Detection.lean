module

public import SerrePositivity.HomotopicalAlgebra.Localization.Basic
public import SerrePositivity.HomotopicalAlgebra.Quillen.Saturation
public import SerrePositivity.HomotopicalAlgebra.Simplicial.PiZeroWeakEquivalence
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.PiZero

/-! # Detection of the original weak equivalences and empty localization

The actual π₀ comparison identifies all mapping tests with precomposition
on the ordinary localization. The resulting isomorphism is detected by
the proved saturation theorem, not by an additional conservativity input.
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

include hfib in
lemma chosenMappingSpace_isFibrant (X : Cᵒᵖ) (Y : C) :
    IsFibrant (((chosenResolutionHom cof fib).obj X).obj Y) := by
  constructor
  rw [hfib]
  exact (SSet.modelCategoryQuillen.fibration_iff _).mp
    (chosenResolutionHom_kanComplex cof fib X Y)

include hcof hfib in
lemma weakEquivalence_of_mappingTests {X Y : C} (f : X ⟶ Y)
    (hf : ∀ Z, mappingTest cof fib Z f) : weakEquivalences C f := by
  let L := (weakEquivalences C).Q
  have hpre (Z : C) :
      Function.Bijective (fun k : L.obj Y ⟶ L.obj Z => L.map f ≫ k) := by
    have := chosenMappingSpace_isFibrant cof fib hfib (Opposite.op X) Z
    have := chosenMappingSpace_isFibrant cof fib hfib (Opposite.op Y) Z
    have : WeakEquivalence (((chosenResolutionHom cof fib).map f.op).app Z) := ⟨hf Z⟩
    have hb := SimplicialModel.piZero_bijective_of_weakEquivalence_of_fibrant hcof
      (((chosenResolutionHom cof fib).map f.op).app Z)
    let eX := chosenResolutionHomPiZeroEquiv L cof fib (Opposite.op X) Z
    let eY := chosenResolutionHomPiZeroEquiv L cof fib (Opposite.op Y) Z
    have hnat (z) : eX (SSet.mapπ₀ (((chosenResolutionHom cof fib).map f.op).app Z) z) =
        L.map f ≫ eY z :=
      chosenResolutionHomPiZeroEquiv_naturality_source L cof fib f.op Z z
    have hb' := eX.bijective.comp (hb.comp eY.symm.bijective)
    simpa only [Function.comp_def, hnat, Equiv.apply_symm_apply] using hb'
  obtain ⟨g, hg⟩ := (hpre X).surjective (𝟙 (L.obj X))
  have hg' : g ≫ L.map f = 𝟙 (L.obj Y) := (hpre Y).injective (by
    simp only [← Category.assoc, hg, Category.id_comp, Category.comp_id])
  have : IsIso (L.map f) := ⟨g, hg, hg'⟩
  exact (Quillen.weakEquivalences_iff_isIso_map L f).mpr inferInstance

include hcof hfib in
lemma weakEquivalences_iff_mappingTests {X Y : C} (f : X ⟶ Y) :
    weakEquivalences C f ↔ ∀ Z, mappingTest cof fib Z f :=
  ⟨fun hf Z => weakEquivalences_le_mappingTest cof fib hcof Z f hf,
    weakEquivalence_of_mappingTests cof fib hcof hfib f⟩

include hcof hfib in
lemma localEquivalences_eq_weakEquivalences_of_le {S : MorphismProperty C}
    (hS : S ≤ weakEquivalences C) : localEquivalences cof fib S = weakEquivalences C := by
  apply le_antisymm
  · intro X Y f hf
    exact weakEquivalence_of_mappingTests cof fib hcof hfib f
      (fun Z => hf Z (localObjects_of_le_weakEquivalences cof fib hcof hS Z))
  · exact weakEquivalences_le_localEquivalences cof fib hcof S

include hcof hfib in
lemma localEquivalences_bot : localEquivalences cof fib ⊥ = weakEquivalences C :=
  localEquivalences_eq_weakEquivalences_of_le cof fib hcof hfib bot_le

include hcof in
lemma localFibrantObjects_iff_of_le {S : MorphismProperty C} (hS : S ≤ weakEquivalences C)
    (Y : C) : localFibrantObjects cof fib S Y ↔ IsFibrant Y :=
  ⟨And.left, fun hY => ⟨hY, localObjects_of_le_weakEquivalences cof fib hcof hS Y⟩⟩

end SerrePositivity.Bousfield
