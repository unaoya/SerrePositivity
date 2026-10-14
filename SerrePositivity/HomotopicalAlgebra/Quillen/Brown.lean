module

public import SerrePositivity.HomotopicalAlgebra.Quillen.Adjunction
public import Mathlib.AlgebraicTopology.ModelCategory.BrownLemma

/-!
# Ken Brown preservation for Quillen functors

Preservation of trivial cofibrations/fibrations implies preservation of weak
equivalences on cofibrant/fibrant objects, using Mathlib's Brown factorizations.
This does not claim preservation of all weak equivalences.
-/

@[expose] public section

universe u₁ v₁ u₂ v₂

open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Quillen

variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
  {D : Type u₂} [Category.{v₂} D] [ModelCategory D]

lemma map_weakEquivalence_of_cofibrant (L : C ⥤ D) [IsLeftQuillen L]
    {X Y : C} [IsCofibrant X] [IsCofibrant Y] (f : X ⟶ Y) [WeakEquivalence f] :
    WeakEquivalence (L.map f) := by
  let h := Classical.choice (inferInstance : Nonempty (CofibrantBrownFactorization f))
  have : Cofibration h.i := (cofibration_iff _).2 h.hi
  have : WeakEquivalence (L.map h.i) := map_weakEquivalence_of_cofibration L h.i
  have : WeakEquivalence (L.map h.s) := map_weakEquivalence_of_cofibration L h.s
  have hs : L.map h.s ≫ L.map h.p = 𝟙 _ := by rw [← L.map_comp, h.s_p, L.map_id]
  have : WeakEquivalence (L.map h.p) := weakEquivalence_of_precomp_of_fac hs
  rw [← h.fac, L.map_comp]
  infer_instance

lemma map_weakEquivalence_of_fibrant (R : D ⥤ C) [IsRightQuillen R]
    {X Y : D} [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y) [WeakEquivalence f] :
    WeakEquivalence (R.map f) := by
  let h := Classical.choice (inferInstance : Nonempty (FibrantBrownFactorization f))
  have : Fibration h.p := (fibration_iff _).2 h.hp
  have : WeakEquivalence (R.map h.p) := map_weakEquivalence_of_fibration R h.p
  have : WeakEquivalence (R.map h.r) := map_weakEquivalence_of_fibration R h.r
  have hr : R.map h.i ≫ R.map h.r = 𝟙 _ := by rw [← R.map_comp, h.i_r, R.map_id]
  have : WeakEquivalence (R.map h.i) := weakEquivalence_of_postcomp_of_fac hr
  rw [← h.fac, R.map_comp]
  infer_instance

end SerrePositivity.Quillen
