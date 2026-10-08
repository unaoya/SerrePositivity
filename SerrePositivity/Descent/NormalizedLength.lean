module

public import SerrePositivity.OrdinaryEuler
public import SerrePositivity.NormalizedEuler
public import SerrePositivity.Koszul
public import Mathlib.RingTheory.Noetherian.Nilpotent

/-!
# Normalized-length part of Lemma 3.5a

The normalized-length evaluation lives here so that this proof can be
developed independently of the ordinary evaluation and Lemma 3.5b/c.
The length is abstract; no specific perfectoid algebra or tower is required.
The hypotheses of Lemma 3.5a (`A` Noetherian local, `z` a system of parameters,
`T` finite over `A`, `λ H_j(z^v; C) < ∞`) are taken directly as arguments.
-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing
open scoped ENNReal

namespace SerrePositivity

variable {A T C : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing T]
  [Algebra A T] [Module.Finite A T] [CommRing C] [Algebra T C] [Algebra A C] [IsScalarTower A T C]
  {e : ℕ} {z : Fin e → A} {lam : NormalizedLength C ((maximalIdeal A).map (algebraMap A C))}

/-- Supported homology belongs to the power-torsion category. -/
lemma supported_homology_isPowTorsion {J : Ideal C} (hfg : J.FG) {n : ℕ}
    {w : Fin n → C} (hJ : J ≤ (Ideal.span (Set.range w)).radical)
    {P : CochainComplex (ModuleCat.{u} C) ℤ} (hP : IsSupported w P) (i : ℤ) :
    IsPowTorsion J (P.homology i) := by
  have hAnn : J ≤ (Module.annihilator C (P.homology i)).radical :=
    hJ.trans (by
      have h := Ideal.radical_mono (hP.le_radical_annihilator i)
      simpa only [Ideal.radical_idem] using h)
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hAnn hfg
  refine ⟨n, ?_⟩
  rw [Module.isTorsionBySet_iff_subset_annihilator, SetLike.coe_subset_coe]
  exact hn

omit [Module.Finite A T] in
/-- Base-changed supported complexes have homology in the domain of `λ`. -/
lemma chiLam_homology_isPowTorsion
    (hz : (Ideal.span (Set.range z)).radical = maximalIdeal A)
    {P : CochainComplex (ModuleCat.{u} T) ℤ}
    (hP : IsPerfectSupported (algebraMap A T ∘ z) P) (i : ℤ) :
    IsPowTorsion ((maximalIdeal A).map (algebraMap A C))
      ((baseChange (algebraMap T C) P).homology i) := by
  have hfg := (maximalIdeal A).fg_of_isNoetherianRing.map (algebraMap A C)
  have hJ : (maximalIdeal A).map (algebraMap A C) ≤
      (Ideal.span (Set.range (algebraMap A C ∘ z))).radical := by
    have h := Ideal.map_radical_le (algebraMap A C) (I := Ideal.span (Set.range z))
    rw [hz, Ideal.map_span, ← Set.range_comp] at h
    exact h
  have hs : IsSupported (algebraMap A C ∘ z) (baseChange (algebraMap T C) P) := by
    have h := isSupported_baseChange (algebraMap T C) hP.supported
    have heq : algebraMap T C ∘ (algebraMap A T ∘ z) = algebraMap A C ∘ z := by
      funext j
      exact (IsScalarTower.algebraMap_apply A T C (z j)).symm
    rwa [heq] at h
  exact supported_homology_isPowTorsion hfg hJ hs i

omit [Algebra T C] in
/-- Coefficient extension preserves bounds on a complex. -/
lemma baseChange_bounded (φ : T →+* C) (P : CochainComplex (ModuleCat.{u} T) ℤ)
    (hP : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (P.X i)) :
    ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero ((baseChange φ P).X i) := by
  obtain ⟨a, b, hab⟩ := hP
  exact ⟨a, b, fun i hi ↦ (ModuleCat.extendScalars φ).map_isZero (hab i hi)⟩

omit [IsNoetherianRing A] [Algebra A T] [Algebra T C] [IsScalarTower A T C] in
/-- Normalized Euler evaluation is invariant under homotopy equivalence. -/
lemma chiLam_eq_of_homotopyEquiv (φ : T →+* C)
    {P Q : CochainComplex (ModuleCat.{u} T) ℤ} (h : HomotopyEquiv P Q) :
    chiLam lam φ P = chiLam lam φ Q :=
  lambdaEuler_eq_of_homotopyEquiv lam ((ModuleCat.extendScalars φ).mapHomotopyEquiv h)

/-- The remaining Koszul finiteness argument: use a positive common exponent
from the null homotopies, show finite evaluations for the Koszul tensor complex
by a finite filtration, and extract the original homology as a retract. -/
theorem lemma_3_5a_lam_finite
    (_hz : (Ideal.span (Set.range z)).radical = maximalIdeal A)
    (_hfin : ∀ (v j : ℕ),
      lam.len (koszulHomologySelf (fun k ↦ algebraMap A C (z k ^ v)) j) ≠ ⊤)
    (P : PerfSupp T (algebraMap A T ∘ z)) (i : ℤ) :
    lam.len ((baseChange (algebraMap T C) P.1).homology i) ≠ ⊤ := by
  sorry

omit [Module.Finite A T] in
/-- Mapping-cone additivity assuming finite homology evaluations. -/
lemma chiLam_cone_of_finite
    (hz : (Ideal.span (Set.range z)).radical = maximalIdeal A)
    (hfinite : ∀ (P : PerfSupp T (algebraMap A T ∘ z)) (i : ℤ),
      lam.len ((baseChange (algebraMap T C) P.1).homology i) ≠ ⊤)
    (P Q : PerfSupp T (algebraMap A T ∘ z)) (f : P.1 ⟶ Q.1)
    (hc : IsPerfectSupported (algebraMap A T ∘ z) (CochainComplex.mappingCone f)) :
    chiLam lam (algebraMap T C) (CochainComplex.mappingCone f) =
      chiLam lam (algebraMap T C) Q.1 - chiLam lam (algebraMap T C) P.1 := by
  let F := ModuleCat.extendScalars.{u, u, u} (algebraMap T C)
  let fC := (F.mapHomologicalComplex (ComplexShape.up ℤ)).map f
  let k : baseChange (algebraMap T C) (CochainComplex.mappingCone f) ≅ Cone.cone fC :=
    HomologicalComplex.homotopyCofiber.mapHomologicalComplexObjIso f F
  have hbound : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero ((Cone.cone fC).X i) := by
    obtain ⟨a, b, hab⟩ := baseChange_bounded (algebraMap T C) _ hc.bounded
    exact ⟨a, b, fun i hi ↦ (HomologicalComplex.Hom.isoApp k i).isZero_iff.mp (hab i hi)⟩
  have tC : ∀ i, IsPowTorsion ((maximalIdeal A).map (algebraMap A C))
      ((Cone.cone fC).homology i) := fun i ↦
    IsPowTorsion.of_equiv
      (((HomologicalComplex.homologyFunctor _ _ i).mapIso k).toLinearEquiv)
      (chiLam_homology_isPowTorsion hz hc i)
  have lC : ∀ i, lam.len ((Cone.cone fC).homology i) ≠ ⊤ := by
    intro i
    have hi := lam.len_congr _ _
      (((HomologicalComplex.homologyFunctor _ _ i).mapIso k).toLinearEquiv)
    exact ne_of_eq_of_ne hi.symm (hfinite ⟨_, hc⟩ i)
  change lambdaEuler lam (baseChange (algebraMap T C) (CochainComplex.mappingCone f)) =
    lambdaEuler lam (baseChange (algebraMap T C) Q.1) -
      lambdaEuler lam (baseChange (algebraMap T C) P.1)
  rw [lambdaEuler_eq_of_homotopyEquiv lam (HomotopyEquiv.ofIso k)]
  exact lambdaEuler_cone lam fC
    (baseChange_bounded (algebraMap T C) _ Q.2.bounded) hbound
    (chiLam_homology_isPowTorsion hz P.2) (chiLam_homology_isPowTorsion hz Q.2) tC
    (hfinite P) (hfinite Q) lC

/-- Finite evaluations let the normalized Euler evaluation descend to `K₀`. -/
noncomputable def chiLamHom_of_finite
    (hz : (Ideal.span (Set.range z)).radical = maximalIdeal A)
    (hfinite : ∀ (P : PerfSupp T (algebraMap A T ∘ z)) (i : ℤ),
      lam.len ((baseChange (algebraMap T C) P.1).homology i) ≠ ⊤) :
    K0Supported T (algebraMap A T ∘ z) →+ ℝ :=
  K0.lift (fun P ↦ chiLam lam (algebraMap T C) P.1)
    (fun _ _ h ↦ chiLam_eq_of_homotopyEquiv (algebraMap T C) h)
    (chiLam_cone_of_finite hz hfinite)

omit [Module.Finite A T] in
@[simp]
lemma chiLamHom_of_finite_mk
    (hz : (Ideal.span (Set.range z)).radical = maximalIdeal A)
    (hfinite : ∀ (P : PerfSupp T (algebraMap A T ∘ z)) (i : ℤ),
      lam.len ((baseChange (algebraMap T C) P.1).homology i) ≠ ⊤)
    (P : PerfSupp T (algebraMap A T ∘ z)) :
    chiLamHom_of_finite hz hfinite (K0.mk P) = chiLam lam (algebraMap T C) P.1 :=
  K0.lift_mk _ _ _ _

/-- **Lemma 3.5a, normalized length**: the independent normalized-length
assertion. Only the Koszul finiteness step remains unproved. -/
theorem lemma_3_5a_lam
    (hz : (Ideal.span (Set.range z)).radical = maximalIdeal A)
    (hfin : ∀ (v j : ℕ),
      lam.len (koszulHomologySelf (fun k ↦ algebraMap A C (z k ^ v)) j) ≠ ⊤) :
    (∀ (P : PerfSupp T (algebraMap A T ∘ z)) (i : ℤ),
      lam.len ((baseChange (algebraMap T C) P.1).homology i) ≠ ⊤) ∧
      (∃ χ : K0Supported T (algebraMap A T ∘ z) →+ ℝ,
        ∀ P, χ (K0.mk P) = chiLam lam (algebraMap T C) P.1) := by
  have hfinite := lemma_3_5a_lam_finite (T := T) hz hfin
  exact ⟨hfinite, chiLamHom_of_finite hz hfinite, chiLamHom_of_finite_mk hz hfinite⟩

end SerrePositivity
