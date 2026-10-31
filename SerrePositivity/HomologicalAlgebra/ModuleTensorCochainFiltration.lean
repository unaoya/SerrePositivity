module
public import SerrePositivity.HomologicalAlgebra.NilpotentModuleFiltration
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Cone
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.RingTheory.Flat.CategoryTheory

/-! # Nilpotent coefficient filtrations in tensoring with a flat cochain complex -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex
variable {R : Type u} [CommRing R]

/-- Tensor every varying coefficient module with the same cochain complex. -/
def moduleTensorCochainFunctor (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    ModuleCat.{u} R ⥤ CochainComplex (ModuleCat.{u} R) ℤ where
  obj N := ((tensorLeft N).mapHomologicalComplex (.up ℤ)).obj K
  map f := (NatTrans.mapHomologicalComplex ((tensoringLeft (ModuleCat R)).map f) (.up ℤ)).app K
  map_id N := by
    rw [CategoryTheory.Functor.map_id, NatTrans.mapHomologicalComplex_id]
    rfl
  map_comp f g := by
    rw [CategoryTheory.Functor.map_comp, NatTrans.mapHomologicalComplex_comp]
    rfl

/-- The original coefficient tensor functor is additive on all module maps. -/
instance moduleTensorCochainFunctor_additive (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (moduleTensorCochainFunctor K).Additive where
  map_add {X Y f g} := by
    apply HomologicalComplex.Hom.ext
    funext i
    change ((tensoringLeft (ModuleCat R)).map (f + g)).app (K.X i) = _
    rw [CategoryTheory.Functor.map_add]
    rfl

/-- Termwise flatness preserves every original short exact sequence of coefficients. -/
lemma moduleTensorCochain_shortExact (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : ∀ i, Module.Flat R (K.X i)) (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) : (S.map (moduleTensorCochainFunctor K)).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  intro i
  let := hK i
  exact hS.map_of_exact (tensorRight (K.X i))

/-- Vanishing in any fixed degree is extension-closed in the coefficient module. -/
lemma moduleTensorCochain_homology_isZero_extension
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : ∀ i, Module.Flat R (K.X i))
    (i : ℤ) (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (h₁ : IsZero (((moduleTensorCochainFunctor K).obj S.X₁).homology i))
    (h₃ : IsZero (((moduleTensorCochainFunctor K).obj S.X₃).homology i)) :
    IsZero (((moduleTensorCochainFunctor K).obj S.X₂).homology i) := by
  have he := (moduleTensorCochain_shortExact K hK S hS).homology_exact₂ i
  exact he.isZero_X₂ (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)

/-- Nilpotence extends coefficientwise homology vanishing from residue modules to all modules. -/
lemma moduleTensorCochain_homology_isZero_of_nilpotentIdeal
    (I : Ideal R) (hNil : ∃ n : ℕ, I ^ n = ⊥)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : ∀ i, Module.Flat R (K.X i))
    (i : ℤ)
    (hI : ∀ N : ModuleCat.{u} R, (∀ r ∈ I, ∀ x : N, r • x = 0) →
      IsZero (((moduleTensorCochainFunctor K).obj N).homology i))
    (N : ModuleCat.{u} R) : IsZero (((moduleTensorCochainFunctor K).obj N).homology i) :=
  moduleProperty_of_nilpotentIdeal I hNil _ hI
    (moduleTensorCochain_homology_isZero_extension K hK i) N

/-- The unresolved coefficient ring tensors to the original complex by the standard unitor. -/
def moduleTensorCochainUnitIso (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (moduleTensorCochainFunctor K).obj (ModuleCat.of R R) ≅ K :=
  (cochainTensorSingleLeftIso (ModuleCat.of R R) K).symm ≪≫ cochainTensorLeftUnitor K

/-- In particular residue-module tests detect each vanishing degree of the original complex. -/
lemma cochain_homology_isZero_of_nilpotentIdeal_tests
    (I : Ideal R) (hNil : ∃ n : ℕ, I ^ n = ⊥)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : ∀ i, Module.Flat R (K.X i))
    (i : ℤ)
    (hI : ∀ N : ModuleCat.{u} R, (∀ r ∈ I, ∀ x : N, r • x = 0) →
      IsZero (((moduleTensorCochainFunctor K).obj N).homology i)) :
    IsZero (K.homology i) :=
  ((homologyFunctor (ModuleCat R) (.up ℤ) i).mapIso
    (moduleTensorCochainUnitIso K)).isZero_iff.mp
      (moduleTensorCochain_homology_isZero_of_nilpotentIdeal I hNil K hK i hI
        (ModuleCat.of R R))

end SerrePositivity
