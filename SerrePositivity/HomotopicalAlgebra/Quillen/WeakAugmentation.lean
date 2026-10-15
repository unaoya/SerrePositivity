module

public import SerrePositivity.HomotopicalAlgebra.Quillen.Brown

/-! # Transferring realization of a weak augmentation to a cofibrant replacement -/

@[expose] public section
universe v u v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Quillen
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {D : Type u'} [Category.{v'} D] [ModelCategory D]

lemma map_trivialFibration_of_weakAugmentation
    (L : C ⥤ D) [IsLeftQuillen L] {A B X : C} [IsCofibrant A] [IsCofibrant B]
    (f : A ⟶ X) (p : B ⟶ X) (hf : weakEquivalences C f)
    (hp : trivialFibrations C p) (hLf : weakEquivalences D (L.map f)) :
    weakEquivalences D (L.map p) := by
  have : Fibration p := ⟨hp.1⟩
  have : WeakEquivalence p := ⟨hp.2⟩
  have sq : CommSq (initial.to B) (initial.to A) p f := ⟨by simp⟩
  have hl : weakEquivalences C sq.lift :=
    (weakEquivalences C).of_postcomp _ _ hp.2 (sq.fac_right.symm ▸ hf)
  have : WeakEquivalence sq.lift := ⟨hl⟩
  have hLl : weakEquivalences D (L.map sq.lift) :=
    (weakEquivalence_iff _).mp (map_weakEquivalence_of_cofibrant L sq.lift)
  apply (weakEquivalences D).of_precomp _ _ hLl
  rw [← L.map_comp, sq.fac_right]
  exact hLf

end SerrePositivity.Quillen
