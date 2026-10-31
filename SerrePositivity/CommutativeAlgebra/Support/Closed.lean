module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Sets.Closeds
public import SerrePositivity.CommutativeAlgebra.Localization.PowerTorsion
public import Mathlib.RingTheory.Support
public import SerrePositivity.CommutativeAlgebra.Length.Basic
public import SerrePositivity.CommutativeAlgebra.SupportDimension

/-! # 素スペクトル上の閉台

## 概要

イデアルの零点集合 `supportZeroLocus` と環準同型による逆像 `supportPullback`、その単調性・積・冪との関係、加法的な族での主台の結合 `principalSupport_add`、完全列の中央の台が両端の台の和に含まれることと零化元による台の評価、有限加群の閉台 `finiteModuleClosedSupport`（台を含み、極大イデアルとの交わりで抑えられる）を与える。

## 方針

閉台は `PrimeSpectrum.zeroLocus` と `PrimeSpectrum.comap` で書き、加群の閉台は `Module.annihilator` の零点集合とする。

## 規約

台つきの K 理論・完全複体で使う閉集合の言葉を一か所に集める。

## 使われ方

KTheory の台つき加群・G0 の関手性・ねじれの零化・局所化の核、PerfectComplex の閉台とその関手性・テンソルの基底変換・Tor の比較、CommutativeAlgebra/SupportHeight・ModuleSupportHeight。
-/

@[expose] public noncomputable section

universe u v

section ClosedSupportGeometryPart

namespace SerrePositivity
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- イデアルの零点集合を閉集合として扱う。 -/
def supportZeroLocus (I : Ideal R) : TopologicalSpace.Closeds (PrimeSpectrum R) :=
  ⟨PrimeSpectrum.zeroLocus I, PrimeSpectrum.isClosed_zeroLocus (I : Set R)⟩

@[simp] lemma coe_supportZeroLocus (I : Ideal R) :
    (supportZeroLocus I : Set (PrimeSpectrum R)) = PrimeSpectrum.zeroLocus I := rfl

/-- 台の指定はイデアルの零点集合だけに依存する。 -/
lemma supportZeroLocus_eq {I J : Ideal R}
    (h : PrimeSpectrum.zeroLocus I = PrimeSpectrum.zeroLocus (J : Set R)) :
    supportZeroLocus I = supportZeroLocus J := SetLike.coe_injective h

/-- Pull back a closed support along the map of prime spectra. -/
def supportPullback (φ : R →+* S) (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) :
    TopologicalSpace.Closeds (PrimeSpectrum S) :=
  ⟨(PrimeSpectrum.comap φ) ⁻¹' Z, Z.isClosed.preimage (PrimeSpectrum.continuous_comap φ)⟩

@[simp] lemma mem_supportPullback (φ : R →+* S)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) (p : PrimeSpectrum S) :
    p ∈ supportPullback φ Z ↔ PrimeSpectrum.comap φ p ∈ Z := Iff.rfl

@[simp] lemma supportPullback_id (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) :
    supportPullback (RingHom.id R) Z = Z := by
  ext p
  simp [supportPullback, PrimeSpectrum.comap_id]

@[simp] lemma supportPullback_comp (φ : R →+* S) (ψ : S →+* T)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) :
    supportPullback ψ (supportPullback φ Z) = supportPullback (ψ.comp φ) Z := by
  ext p
  simp [supportPullback]

lemma supportPullback_mono (φ : R →+* S)
    {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)} (h : Z ≤ W) :
    supportPullback φ Z ≤ supportPullback φ W := by
  intro p hp
  exact h hp

@[simp] lemma supportPullback_zeroLocus (φ : R →+* S) (I : Ideal R) :
    supportPullback φ (supportZeroLocus I) = supportZeroLocus (I.map φ) := by
  ext p
  change I ≤ p.asIdeal.comap φ ↔ I.map φ ≤ p.asIdeal
  exact Ideal.map_le_iff_le_comap.symm

/-- Pullback of a support specified by a generating list. -/
lemma supportPullback_span (φ : R →+* S) {e : ℕ} (z : Fin e → R) :
    supportPullback φ (supportZeroLocus (Ideal.span (Set.range z))) =
      supportZeroLocus (Ideal.span (Set.range (φ ∘ z))) := by
  rw [supportPullback_zeroLocus, Ideal.map_span, ← Set.range_comp]

variable (φ : R →+* S)

/-- Pullback of an intersection lies in an intersection of larger target supports. -/
lemma supportPullback_inf_le {Y Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    {W V : TopologicalSpace.Closeds (PrimeSpectrum S)}
    (hY : supportPullback φ Y ≤ W) (hZ : supportPullback φ Z ≤ V) :
    supportPullback φ (Y ⊓ Z) ≤ W ⊓ V := by
  intro p hp
  exact ⟨hY hp.1, hZ hp.2⟩

lemma supportZeroLocus_mul_left (s t : R) :
    supportZeroLocus (Ideal.span ({s} : Set R)) ≤
      supportZeroLocus (Ideal.span ({s * t} : Set R)) := by
  intro p hp
  change Ideal.span ({s * t} : Set R) ≤ p.asIdeal
  apply Ideal.span_le.mpr
  intro a ha
  have ha' : a = s * t := Set.mem_singleton_iff.mp ha
  subst a
  exact p.asIdeal.mul_mem_right t (hp (Ideal.subset_span (Set.mem_singleton s)))

lemma supportZeroLocus_mul_right (s t : R) :
    supportZeroLocus (Ideal.span ({t} : Set R)) ≤
      supportZeroLocus (Ideal.span ({s * t} : Set R)) := by
  simpa only [mul_comm] using supportZeroLocus_mul_left t s

/-- Vanishing of a power implies vanishing of its base, including the empty locus for n = 0. -/
lemma supportZeroLocus_pow_le (s : R) (n : ℕ) :
    supportZeroLocus (Ideal.span ({s ^ n} : Set R)) ≤
      supportZeroLocus (Ideal.span ({s} : Set R)) := by
  intro p hp
  change Ideal.span ({s} : Set R) ≤ p.asIdeal
  apply Ideal.span_le.mpr
  intro a ha
  obtain rfl := Set.mem_singleton_iff.mp ha
  exact p.isPrime.mem_of_pow_mem n (hp (Ideal.subset_span (Set.mem_singleton _)))

end SerrePositivity

end ClosedSupportGeometryPart

section PrincipalSupportPart

namespace SerrePositivity
variable {R : Type u} [CommRing R]

/-- Compatible support enlargement combines two denominators by their product. -/
lemma principalSupport_add
    (F : TopologicalSpace.Closeds (PrimeSpectrum R) → Type v) [∀ W, AddCommGroup (F W)]
    (enlarge : ∀ {U V}, U ≤ V → F U →+ F V)
    (hcomp : ∀ {U V W} (h : U ≤ V) (h' : V ≤ W) (y : F U),
      enlarge h' (enlarge h y) = enlarge (h.trans h') y)
    {P : Submonoid R} {Z : TopologicalSpace.Closeds (PrimeSpectrum R)} {x x' : F Z}
    (hx : ∃ s ∈ P, ∃ y : F (Z ⊓ supportZeroLocus (Ideal.span ({s} : Set R))),
      enlarge inf_le_left y = x)
    (hx' : ∃ t ∈ P, ∃ y : F (Z ⊓ supportZeroLocus (Ideal.span ({t} : Set R))),
      enlarge inf_le_left y = x') :
    ∃ s ∈ P, ∃ y : F (Z ⊓ supportZeroLocus (Ideal.span ({s} : Set R))),
      enlarge inf_le_left y = x + x' := by
  obtain ⟨s, hs, y, hy⟩ := hx
  obtain ⟨t, ht, y', hy'⟩ := hx'
  let h₁ := inf_le_inf_left Z (supportZeroLocus_mul_left s t)
  let h₂ := inf_le_inf_left Z (supportZeroLocus_mul_right s t)
  refine ⟨s * t, P.mul_mem hs ht, enlarge h₁ y + enlarge h₂ y', ?_⟩
  rw [map_add, hcomp, hcomp, hy, hy']

end SerrePositivity

end PrincipalSupportPart

section ModuleSupportPart

namespace SerrePositivity
variable {R : Type u} [CommRing R]

/-- Exactness alone bounds the middle support by the union of the two outer supports. -/
lemma module_support_subset_union_of_exact
    {M N L : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup L]
    [Module R M] [Module R N] [Module R L]
    (f : M →ₗ[R] N) (g : N →ₗ[R] L) (h : Function.Exact f g) :
    Module.support R N ⊆ Module.support R M ∪ Module.support R L := by
  intro p
  contrapose
  simp only [Set.mem_union, not_or, and_imp, Module.notMem_support_iff']
  intro hM hL
  exact isTorsion'_iff_forall.mp (isTorsion'_of_exact (P := p.asIdeal.primeCompl) f g h
    (isTorsion'_iff_forall.mpr hM) (isTorsion'_iff_forall.mpr hL))

variable {M : Type u} [AddCommGroup M] [Module R M]

/-- An annihilator puts the support in its principal vanishing locus. -/
lemma module_support_subset_zeroLocus_of_annihilator (r : R) (h : ∀ m : M, r • m = 0) :
    Module.support R M ⊆ supportZeroLocus (Ideal.span ({r} : Set R)) := by
  intro p hp
  apply Ideal.span_le.mpr
  intro a ha
  obtain rfl := Set.mem_singleton_iff.mp ha
  exact Module.annihilator_le_of_mem_support hp (Module.mem_annihilator.mpr h)

end SerrePositivity

end ModuleSupportPart

section ModuleClosedSupportPart

namespace SerrePositivity
open IsLocalRing TensorProduct
variable (R : Type u) [CommRing R]

/-- Support of a finite module, represented as the zero locus of its annihilator. -/
def finiteModuleClosedSupport (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    TopologicalSpace.Closeds (PrimeSpectrum R) := supportZeroLocus (Module.annihilator R M)

@[simp]
lemma finiteModuleClosedSupport_coe (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    (finiteModuleClosedSupport R M : Set (PrimeSpectrum R)) = Module.support R M :=
  Module.support_eq_zeroLocus.symm

lemma support_subset_finiteModuleClosedSupport
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Module.support R M ⊆ finiteModuleClosedSupport R M := by
  rw [finiteModuleClosedSupport_coe]

/-- Finite length of the tensor product places the intersection of supports at the closed point. -/
lemma finiteModuleClosedSupport_inf_le_maximal [IsLocalRing R]
    (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N]
    (hfin : Module.length R (M ⊗[R] N) ≠ ⊤) :
    finiteModuleClosedSupport R M ⊓ finiteModuleClosedSupport R N ≤
      supportZeroLocus (maximalIdeal R) := by
  intro p hp
  have hM : p ∈ Module.support R M := by
    simpa only [← finiteModuleClosedSupport_coe R M] using hp.1
  have hN : p ∈ Module.support R N := by
    simpa only [← finiteModuleClosedSupport_coe R N] using hp.2
  have ht : p ∈ Module.support R (M ⊗[R] N) := by
    rw [support_tensorProduct]
    exact ⟨hM, hN⟩
  have he := eq_maximalIdeal
    (isMaximal_of_mem_support_of_isFiniteLength (M ⊗[R] N) (Module.length_ne_top_iff.mp hfin) p ht)
  change maximalIdeal R ≤ p.asIdeal
  exact le_of_eq he.symm
/-- 整域上でスペクトルが全射なら、環準同型は単射。
零素イデアルの逆像となる素イデアルに核が含まれることを使う。 -/
lemma algebraMap_injective_of_spectrum_surjective
    (A T : Type u) [CommRing A] [IsDomain A] [CommRing T] [Algebra A T]
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap A T))) :
    Function.Injective (algebraMap A T) := by
  obtain ⟨q, hq⟩ := hsurj ⟨⊥, inferInstance⟩
  apply (RingHom.injective_iff_ker_eq_bot _).mpr
  apply le_antisymm _ bot_le
  intro a ha
  have h : a ∈ (PrimeSpectrum.comap (algebraMap A T) q).asIdeal := by
    change algebraMap A T a ∈ q.asIdeal
    rw [show algebraMap A T a = 0 from ha]
    exact q.asIdeal.zero_mem
  simpa only [hq] using h

end SerrePositivity

end ModuleClosedSupportPart
