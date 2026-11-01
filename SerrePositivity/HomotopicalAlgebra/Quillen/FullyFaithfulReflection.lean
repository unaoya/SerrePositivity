module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.FullyFaithfulLifting
public import SerrePositivity.HomotopicalAlgebra.Quillen.Brown

/-! # Weak-equivalence reflection without an adjoint

A fully faithful functor preserving cofibrations, fibrations and trivial
fibrations reflects all weak equivalences. The proof factors a source map
and reflects the lifting properties of its cofibration factor.
-/

@[expose] public section
universe v u v' u'
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Quillen
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {D : Type u'} [Category.{v'} D] [ModelCategory D]
  (F : C ⥤ D) [F.Full] [F.Faithful] [IsRightQuillen F]

lemma weakEquivalence_of_map
    (hcof : cofibrations C ≤ (cofibrations D).inverseImage F)
    {X Y : C} (f : X ⟶ Y) (hf : weakEquivalences D (F.map f)) :
    weakEquivalences C f := by
  let d := MorphismProperty.factorizationData (cofibrations C) (trivialFibrations C) f
  have : Fibration d.p := ⟨d.hp.1⟩
  have : WeakEquivalence d.p := ⟨d.hp.2⟩
  have hp : weakEquivalences D (F.map d.p) :=
    (weakEquivalence_iff _).mp (map_weakEquivalence_of_fibration F d.p)
  have hi : weakEquivalences D (F.map d.i) := (weakEquivalences D).of_postcomp _ _ hp
    ((F.map_comp _ _).symm.trans (congrArg F.map d.fac) |>.symm ▸ hf)
  have : Cofibration (F.map d.i) := ⟨hcof _ d.hi⟩
  have : WeakEquivalence (F.map d.i) := ⟨hi⟩
  have hleft : (fibrations C).llp d.i := by
    intro A B p hp
    have : Fibration p := ⟨hp⟩
    have : Fibration (F.map p) := map_fibration F p
    exact (ModelGeneration.hasLiftingProperty_map_iff F d.i p).mp inferInstance
  have hi' : weakEquivalences C d.i := ((fibrations_llp C) ▸ hleft).2
  exact d.fac ▸ (weakEquivalences C).comp_mem d.i d.p hi' d.hp.2

end SerrePositivity.Quillen
