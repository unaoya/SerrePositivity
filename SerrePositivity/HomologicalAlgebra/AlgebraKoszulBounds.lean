module
public import SerrePositivity.HomologicalAlgebra.AlgebraKoszulColimit
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-! # Finite bounds and the integer model of coefficient-algebra Koszul colimits -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {R C : Type u} [CommRing R] [CommRing C] [Algebra R C]
variable {e : ℕ} (z : Fin e → R)

/-- The actual coefficient-algebra dual has no terms above the length of the sequence. -/
lemma algebraKoszulDual_isZero_X (M : ModuleCat.{u} C) (i : ℕ) (hi : e < i) :
    IsZero (((algebraKoszulDualFunctor (C := C) z).obj M).X i) := by
  have hz : IsZero ((toChain (koszulComplex z)).X i) :=
    (koszulComplex_isZero_X_of_lt z (-(i : ℤ)) (by omega)).of_iso
      ((koszulComplex z).restrictionXIso embUp (i := i) (by simp [embUp]))
  have : Subsingleton (((algebraKoszulDualFunctor (C := C) z).obj M).X i) :=
    ⟨fun f g => hz.eq_of_src f g⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- The bound holds as an entire coefficient functor at each term of the power diagram. -/
lemma algebraKoszulDualFunctorComplexDiagram_isZero_X (n i : ℕ) (hi : e < i) :
    IsZero (((algebraKoszulDualFunctorComplexDiagram (C := C) z).obj n).X i) := by
  apply Functor.isZero
  intro M
  exact algebraKoszulDual_isZero_X (C := C) (fun j => z j ^ n) M i hi

/-- Taking the actual complex colimit preserves the finite term bound. -/
lemma algebraKoszulDualColimitComplex_isZero_X (i : ℕ) (hi : e < i) :
    IsZero ((algebraKoszulDualColimitComplex (C := C) z).X i) := by
  let D := algebraKoszulDualFunctorComplexDiagram (C := C) z ⋙
    eval (ModuleCat.{u} C ⥤ ModuleCat.{u} C) (.up ℕ) i
  have hD : IsZero D := Functor.isZero _ (fun n =>
    algebraKoszulDualFunctorComplexDiagram_isZero_X (C := C) z n i hi)
  exact ((colimit.isColimit D).isZero_pt hD).of_iso
    (preservesColimitIso (eval (ModuleCat.{u} C ⥤ ModuleCat.{u} C) (.up ℕ) i)
      (algebraKoszulDualFunctorComplexDiagram (C := C) z))

/-- The term bound holds for every actual C-module of coefficients. -/
lemma algebraKoszulDualColimitFunctor_isZero_X (M : ModuleCat.{u} C)
    (i : ℕ) (hi : e < i) :
    IsZero (((algebraKoszulDualColimitFunctor (C := C) z).obj M).X i) :=
  (algebraKoszulDualColimitComplex_isZero_X (C := C) z i hi).obj M

/-- Extend by zero to integer degrees, for scalar cones and parameter Koszul operators. -/
def algebraKoszulDualIntegerColimitFunctor : ModuleCat.{u} C ⥤
    CochainComplex (ModuleCat.{u} C) ℤ :=
  algebraKoszulDualColimitFunctor (C := C) z ⋙
    nonnegativeCochainEmbedding.extendFunctor (ModuleCat.{u} C)

/-- The integer model vanishes in negative degrees. -/
lemma algebraKoszulDualIntegerColimit_isZero_X_of_neg (M : ModuleCat.{u} C)
    (i : ℤ) (hi : i < 0) :
    IsZero (((algebraKoszulDualIntegerColimitFunctor (C := C) z).obj M).X i) := by
  apply HomologicalComplex.isZero_extend_X
  intro n hn
  change (n : ℤ) = i at hn
  omega

/-- The integer model vanishes above the length of the original sequence. -/
lemma algebraKoszulDualIntegerColimit_isZero_X_of_gt (M : ModuleCat.{u} C)
    (i : ℤ) (hi : (e : ℤ) < i) :
    IsZero (((algebraKoszulDualIntegerColimitFunctor (C := C) z).obj M).X i) := by
  have hnonneg : 0 ≤ i := by omega
  exact (algebraKoszulDualColimitFunctor_isZero_X (C := C) z M i.toNat (by omega)).of_iso
    (((algebraKoszulDualColimitFunctor (C := C) z).obj M).extendXIso
      nonnegativeCochainEmbedding (i := i.toNat) (by
        change (i.toNat : ℤ) = i
        exact Int.toNat_of_nonneg hnonneg))

/-- Extension by zero preserves homology, including its degree-zero boundary, naturally. -/
def algebraKoszulDualIntegerColimitHomologyNatIso (i : ℕ) :
    algebraKoszulDualIntegerColimitFunctor (C := C) z ⋙
        homologyFunctor (ModuleCat.{u} C) (.up ℤ) (i : ℤ) ≅
      algebraKoszulDualColimitFunctor (C := C) z ⋙
        homologyFunctor (ModuleCat.{u} C) (.up ℕ) i :=
  NatIso.ofComponents (fun M =>
    ((algebraKoszulDualColimitFunctor (C := C) z).obj M).extendHomologyIso
      nonnegativeCochainEmbedding (j := i) rfl)
    (fun f => extendHomologyIso_hom_naturality
      ((algebraKoszulDualColimitFunctor (C := C) z).map f)
      nonnegativeCochainEmbedding (j := i) rfl)

/-- The integer model has the same C-ideal annihilator as the nonnegative model. -/
lemma algebraKoszulDualIntegerColimitHomology_annihilator_eq
    (M : ModuleCat.{u} C) (i : ℕ) :
    Module.annihilator C
        (((algebraKoszulDualIntegerColimitFunctor (C := C) z).obj M).homology (i : ℤ)) =
      Module.annihilator C
        (((algebraKoszulDualColimitFunctor (C := C) z).obj M).homology i) := by
  let E := ((algebraKoszulDualIntegerColimitHomologyNatIso (C := C) z i).app M).toLinearEquiv
  apply le_antisymm
  · intro c hc
    rw [Module.mem_annihilator] at hc ⊢
    intro x
    obtain ⟨y, rfl⟩ := E.surjective x
    rw [← E.map_smul, hc, E.map_zero]
  · intro c hc
    rw [Module.mem_annihilator] at hc ⊢
    intro x
    apply E.injective
    rw [E.map_smul, hc, E.map_zero]

/-- Higher Tor annihilation survives passage to the bounded integer C-complex. -/
lemma algebraKoszulDualIntegerColimitHomology_annihilator_of_tor_annihilated
    [IsNoetherian R R]
    (hres : ∀ n : ℕ, IsKoszulResolution (fun j => z j ^ n)) (I : Ideal C)
    (hTor : ∀ (N : ModuleCat.{u} R) (j : ℕ), 0 < j →
      ∀ c ∈ I, torCoefficientScalarEndomorphism C N j c = 0)
    (i : ℕ) (hi : i < e) :
    I ≤ Module.annihilator C
      (((algebraKoszulDualIntegerColimitFunctor (C := C) z).obj
        (ModuleCat.of C C)).homology (i : ℤ)) := by
  rw [algebraKoszulDualIntegerColimitHomology_annihilator_eq]
  exact algebraKoszulDualColimitHomology_annihilator_of_tor_annihilated z hres I hTor i hi

/-- The actual iterated-cone total model of arbitrary parameter Koszul operators
on the coefficient-algebra local-cohomology complex. No regularity of y is assumed. -/
def parameterKoszulColimitFunctor {r : ℕ} (y : Fin r → C) :
    ModuleCat.{u} C ⥤ CochainComplex (ModuleCat.{u} C) ℤ :=
  algebraKoszulDualIntegerColimitFunctor (C := C) z ⋙ koszulFunctor y

end SerrePositivity
