module

public import SerrePositivity.HomotopicalAlgebra.Localization.Endofunctor
public import SerrePositivity.HomotopicalAlgebra.Monoidal.BifunctorChangeModel

/-! # Localizing a Quillen action using derived tensor compatibility

Only the domains of generating cofibrations in the parameter category
are required to be cofibrant. Derived tensor images of S at their two
endpoints must be local equivalences. The resulting pushout-product
axiom is proved for all cofibrations and local trivial cofibrations.
No cofibrancy of generating domains in the localized category is assumed.
-/

@[expose] public section
universe wV wC vV uV vC uC
noncomputable section
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.Bousfield.IsLocalizationModel
variable {V : Type uV} [Category.{vV} V] [base : ModelCategory V]
  {C : Type uC} [Category.{vC} C] [original : ModelCategory C]
  [simplicial : ModelCategory SSet.{vC}]
  {cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C)}
  {fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C)}
  {S : MorphismProperty C} {m : ModelCategory C}
  (h : @IsLocalizationModel C _ original simplicial cof fib S m)
  (hcof : simplicial.categoryWithCofibrations.cofibrations = MorphismProperty.monomorphisms _)
  (hfib : simplicial.categoryWithFibrations.fibrations = SSet.modelCategoryQuillen.J.{vC}.rlp)
  {F : V ⥤ C ⥤ C} {G : Vᵒᵖ ⥤ C ⥤ C} {H : Cᵒᵖ ⥤ C ⥤ V}
  (adj : F ⊣₂ G) (adjFlip : F.flip ⊣₂ H)
  (hF : @Quillen.IsQuillenBifunctor V _ base C _ original C _ original F)
  (IV JV : MorphismProperty V) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{wV} IV JV]
  (IC JC : MorphismProperty C) [@_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{wC} C _ m IC JC]

include h hcof hfib adj adjFlip hF IV JV IC JC in
lemma bifunctor_of_tensor_compatible
    (hdom : ∀ {A B : V} (i : A ⟶ B), IV i → IsCofibrant A)
    (hcompat : ∀ {A B : V} (i : A ⟶ B), IV i → ∀ {X Y : C} (s : X ⟶ Y), S s →
      (@localEquivalences C _ original simplicial cof fib S)
        ((F.obj A).map ((@cofibrantSource C _ original cof).map s)) ∧
      (@localEquivalences C _ original simplicial cof fib S)
        ((F.obj B).map ((@cofibrantSource C _ original cof).map s))) :
    @Quillen.IsQuillenBifunctor V _ base C _ m C _ m F := by
  let := original
  have := hF
  have : ∀ X : C, (F.flip.obj X).IsLeftAdjoint := fun X => (adjFlip.adj X).isLeftAdjoint
  have hw := (weakEquivalences_le_localEquivalences cof fib hcof S).trans
    h.weakEquivalences_eq.symm.le
  apply Quillen.isQuillenBifunctor_change_second adj adjFlip hF h.cofibrations_eq hw IV JV IC JC
  intro A B i hi
  have : IsCofibrant A := hdom i hi
  have : Cofibration i :=
    ⟨(IV.le_llp_rlp.trans (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.cofibrations_eq_generated IV JV).symm.le) i hi⟩
  have : IsCofibrant B := isCofibrant_of_cofibration i
  have hA := Quillen.isLeftQuillen_obj_of_cofibrant F A
  have hB := Quillen.isLeftQuillen_obj_of_cofibrant F B
  exact ⟨(h.endofunctor_isLeftQuillen_iff hcof hfib (adj.adj A) hA).mpr
      (fun s hs => (hcompat i hi s hs).1),
    (h.endofunctor_isLeftQuillen_iff hcof hfib (adj.adj B) hB).mpr
      (fun s hs => (hcompat i hi s hs).2)⟩

end SerrePositivity.Bousfield.IsLocalizationModel
