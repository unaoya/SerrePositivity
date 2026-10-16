module

public import SerrePositivity.HomologicalAlgebra.ModuleTensorCochainFiltration
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.Algebra.Homology.Linear

/-! # Exact coefficient sequences in a fixed flat cochain model -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex
variable {R : Type u} [CommRing R]

instance moduleTensorCochainFunctor_linear (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    Functor.Linear R (moduleTensorCochainFunctor K) where
  map_smul f r := by
    apply HomologicalComplex.Hom.ext
    funext i
    change (tensorRight (K.X i)).map (r • f) = r • (tensorRight (K.X i)).map f
    exact Functor.map_smul _ _ _

/-- Termwise flatness preserves arbitrary exact coefficient sequences,
without requiring the first map to be injective. -/
lemma moduleTensorCochain_exact (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : ∀ i, Module.Flat R (K.X i)) (S : ShortComplex (ModuleCat.{u} R)) (hS : S.Exact) :
    (S.map (moduleTensorCochainFunctor K)).Exact := by
  apply HomologicalComplex.exact_of_degreewise_exact
  intro i
  let := hK i
  change (S.map (tensorRight (K.X i))).Exact
  exact hS.map (tensorRight (K.X i))

/-- Tensoring with a fixed cochain model preserves epimorphisms of coefficients. -/
lemma moduleTensorCochain_map_epi (K : CochainComplex (ModuleCat.{u} R) ℤ)
    {M N : ModuleCat.{u} R} (f : M ⟶ N) [Epi f] :
    Epi ((moduleTensorCochainFunctor K).map f) := by
  apply HomologicalComplex.epi_of_epi_f
  intro i
  change Epi ((tensorRight (K.X i)).map f)
  infer_instance

end SerrePositivity
