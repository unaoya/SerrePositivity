module

public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Adding contractible fibrant parameters preserves weak equivalences

All statements use actual products and their projections. No enrichment
or functorial factorization of the model category is needed.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Quillen.ContractibleParameters
variable {C : Type u} [Category.{v} C] [ModelCategory C] [HasBinaryProducts C]
  {S R Z T V : C} (hZ : IsTerminal Z)
include hZ

lemma projection_trivialFibration (p : S ⟶ Z) (hp : trivialFibrations C p) (V : C) :
    trivialFibrations C (prod.snd : S ⨯ V ⟶ V) := by
  have hp' : trivialFibrations C (hZ.from S) := (hZ.hom_ext p (hZ.from S)) ▸ hp
  exact (trivialFibrations C).of_isPullback
    (IsPullback.of_is_product (prodIsProd S V) hZ) hp'

lemma double_projection_trivialFibration (p : S ⟶ Z) (q : R ⟶ Z)
    (hp : trivialFibrations C p) (hq : trivialFibrations C q) (V : C) :
    trivialFibrations C ((prod.snd : S ⨯ (R ⨯ V) ⟶ R ⨯ V) ≫ prod.snd) :=
  (trivialFibrations C).comp_mem _ _
    (projection_trivialFibration hZ p hp (R ⨯ V)) (projection_trivialFibration hZ q hq V)

lemma graph_weakEquivalence (p : S ⟶ Z) (q : R ⟶ Z)
    (hp : trivialFibrations C p) (hq : trivialFibrations C q)
    (s : T ⟶ S) (r : T ⟶ R) (t : T ⟶ V) (ht : weakEquivalences C t) :
    weakEquivalences C (prod.lift s (prod.lift r t)) := by
  have hπ := double_projection_trivialFibration hZ p q hp hq V
  apply (weakEquivalences C).of_postcomp _ _ hπ.2
  simpa only [← Category.assoc, prod.lift_snd] using ht

end SerrePositivity.Quillen.ContractibleParameters
