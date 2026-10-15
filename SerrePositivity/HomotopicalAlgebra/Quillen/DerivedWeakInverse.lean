module

public import SerrePositivity.HomotopicalAlgebra.Quillen.DerivedComposition

/-! # Actual equivalences of derived functors from weak inverse transformations

The two original functors can both be left Quillen. Weak inverse
transformations on cofibrant objects give both composite isomorphisms and an
equivalence of their ordinary left derived functors. No triangle identity for
the original weak transformations is required: Mathlib's equivalence
constructor supplies the adjusted coherent unit.
-/

@[expose] public section
universe vC uC vD uD vHC uHC vHD uHD
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Quillen
section ToIdentity
variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {HC : Type uHC} [Category.{vHC} HC]
  (Q : C ⥤ HC) [Q.IsLocalization (weakEquivalences C)]
  {F : C ⥤ C} {LF : HC ⥤ HC}
  (α : Q ⋙ LF ⟶ F ⋙ Q)

def leftDerivedToIdentity (τ : F ⟶ 𝟭 C) : LF ⟶ 𝟭 HC := by
  let := Functor.isLeftDerivedFunctor_of_inverts (weakEquivalences C)
    (𝟭 HC) (Functor.rightUnitor Q)
  exact Functor.leftDerivedNatTrans LF (𝟭 HC) α (Functor.rightUnitor Q).hom
    (weakEquivalences C) (Functor.whiskerRight τ Q ≫ (Functor.leftUnitor Q).hom)

lemma leftDerivedToIdentity_app (τ : F ⟶ 𝟭 C) (X : C) :
    (leftDerivedToIdentity Q α τ).app (Q.obj X) = α.app X ≫ Q.map (τ.app X) := by
  let := Functor.isLeftDerivedFunctor_of_inverts (weakEquivalences C)
    (𝟭 HC) (Functor.rightUnitor Q)
  simpa [leftDerivedToIdentity] using
    (Functor.leftDerivedNatTrans_app LF (𝟭 HC) α (Functor.rightUnitor Q).hom
      (weakEquivalences C) (Functor.whiskerRight τ Q ≫ (Functor.leftUnitor Q).hom) X)

variable [IsLeftQuillen F] [LF.IsLeftDerivedFunctor α (weakEquivalences C)]

lemma leftDerivedToIdentity_isIso (τ : F ⟶ 𝟭 C)
    (hτ : ∀ (X : C), IsCofibrant X → WeakEquivalence (τ.app X)) :
    IsIso (leftDerivedToIdentity Q α τ) := by
  apply (isIso_iff_on_cofibrant Q _).mpr
  intro X hX
  have := leftComparison_isIso Q Q α X
  have : IsIso (Q.map (τ.app X)) :=
    Localization.inverts Q (weakEquivalences C) _ ((weakEquivalence_iff _).mp (hτ X hX))
  rw [leftDerivedToIdentity_app]
  infer_instance
end ToIdentity

section WeakInverse
variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {D : Type uD} [Category.{vD} D] [ModelCategory D]
  {HC : Type uHC} [Category.{vHC} HC] {HD : Type uHD} [Category.{vHD} HD]
  (QC : C ⥤ HC) [QC.IsLocalization (weakEquivalences C)]
  (QD : D ⥤ HD) [QD.IsLocalization (weakEquivalences D)]
  {F : C ⥤ D} [F.IsLeftAdjoint] [IsLeftQuillen F]
  {G : D ⥤ C} [G.IsLeftAdjoint] [IsLeftQuillen G]
  {LF : HC ⥤ HD} {LG : HD ⥤ HC}
  (α : QC ⋙ LF ⟶ F ⋙ QD) [LF.IsLeftDerivedFunctor α (weakEquivalences C)]
  (β : QD ⋙ LG ⟶ G ⋙ QC) [LG.IsLeftDerivedFunctor β (weakEquivalences D)]
  (ε : F ⋙ G ⟶ 𝟭 C) (δ : G ⋙ F ⟶ 𝟭 D)
  (hε : ∀ (X : C), IsCofibrant X → WeakEquivalence (ε.app X))
  (hδ : ∀ (Y : D), IsCofibrant Y → WeakEquivalence (δ.app Y))

def derivedWeakInverseEquivalence : HC ≌ HD := by
  letI := leftDerived_comp QC QD QC α β
  letI := leftDerived_comp QD QC QD β α
  let ε' := leftDerivedToIdentity QC (leftCompositeComparison QC QD QC α β) ε
  let δ' := leftDerivedToIdentity QD (leftCompositeComparison QD QC QD β α) δ
  have : IsIso ε' :=
    leftDerivedToIdentity_isIso QC (leftCompositeComparison QC QD QC α β) ε hε
  have : IsIso δ' :=
    leftDerivedToIdentity_isIso QD (leftCompositeComparison QD QC QD β α) δ hδ
  exact CategoryTheory.Equivalence.mk LF LG (asIso ε').symm (asIso δ')

include QC QD α β ε δ hε hδ in
lemma derived_isEquivalence_of_weak_inverse : LF.IsEquivalence :=
  (derivedWeakInverseEquivalence QC QD α β ε δ hε hδ).isEquivalence_functor

end WeakInverse
end SerrePositivity.Quillen
