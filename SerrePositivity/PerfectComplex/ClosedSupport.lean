module

public import SerrePositivity.PerfectComplex.Support
public import SerrePositivity.HomologicalAlgebra.ConeLES
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Sets.Closeds

/-! # 閉集合で指定するホモロジーの台

既存のイデアル・生成列による台を、`Spec R` の閉集合へ拡張する。
複体の有界性・項の有限生成性・射影性は台の定義には要求しない。
-/

@[expose] public section

universe u

namespace SerrePositivity

open CategoryTheory Limits

variable {R : Type u} [CommRing R]

/-- イデアルの零点集合を閉集合として扱う。 -/
def supportZeroLocus (I : Ideal R) : TopologicalSpace.Closeds (PrimeSpectrum R) :=
  ⟨PrimeSpectrum.zeroLocus I, PrimeSpectrum.isClosed_zeroLocus (I : Set R)⟩

@[simp] lemma coe_supportZeroLocus (I : Ideal R) :
    (supportZeroLocus I : Set (PrimeSpectrum R)) = PrimeSpectrum.zeroLocus I := rfl

/-- 全次数のホモロジーの台が閉集合 `Z` に含まれること。 -/
def HasHomologySupportOn (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (P : CochainComplex (ModuleCat.{u} R) ℤ) : Prop :=
  ∀ i, Module.support R (P.homology i) ⊆ Z

/-- 閉集合版の特殊化は既存のイデアル版そのものである。 -/
@[simp] lemma hasHomologySupportOn_zeroLocus (I : Ideal R)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    HasHomologySupportOn (supportZeroLocus I) P ↔ HasHomologySupport I P := Iff.rfl

/-- 台の指定はイデアルの零点集合だけに依存する。 -/
lemma supportZeroLocus_eq {I J : Ideal R}
    (h : PrimeSpectrum.zeroLocus I = PrimeSpectrum.zeroLocus (J : Set R)) :
    supportZeroLocus I = supportZeroLocus J := SetLike.coe_injective h

/-- 台をより大きい閉集合に移す。 -/
lemma HasHomologySupportOn.mono
    {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)}
    {P : CochainComplex (ModuleCat.{u} R) ℤ}
    (hP : HasHomologySupportOn Z P) (hZW : Z ≤ W) : HasHomologySupportOn W P :=
  fun i ↦ (hP i).trans hZW

/-- 二つの台条件の同時成立は交わりの台条件である。 -/
@[simp] lemma hasHomologySupportOn_inf
    (Z W : TopologicalSpace.Closeds (PrimeSpectrum R))
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    HasHomologySupportOn (Z ⊓ W) P ↔
      HasHomologySupportOn Z P ∧ HasHomologySupportOn W P := by
  constructor
  · intro h
    exact ⟨h.mono inf_le_left, h.mono inf_le_right⟩
  · rintro ⟨hZ, hW⟩ i p hp
    exact ⟨hZ i hp, hW i hp⟩

/-- Exactness alone bounds the middle support by the union of the two outer supports. -/
lemma module_support_subset_union_of_exact
    {M N L : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup L]
    [Module R M] [Module R N] [Module R L]
    (f : M →ₗ[R] N) (g : N →ₗ[R] L) (h : Function.Exact f g) :
    Module.support R N ⊆ Module.support R M ∪ Module.support R L := by
  intro x
  contrapose
  simp only [Set.mem_union, not_or, and_imp, Module.notMem_support_iff']
  intro hM hL n
  obtain ⟨r, hr, er⟩ := hL (g n)
  rw [← map_smul, h] at er
  obtain ⟨m, hm⟩ := er
  obtain ⟨t, ht, et⟩ := hM m
  exact ⟨_, x.asIdeal.primeCompl.mul_mem ht hr, by
    rw [mul_smul, ← hm, ← map_smul, et, map_zero]⟩

variable {Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
  {P Q : CochainComplex (ModuleCat.{u} R) ℤ}

/-- A homology isomorphism in each degree preserves the closed support condition. -/
lemma HasHomologySupportOn.of_homologyIso (hP : HasHomologySupportOn Z P)
    (e : ∀ i, P.homology i ≅ Q.homology i) : HasHomologySupportOn Z Q := by
  intro i
  rw [← (e i).toLinearEquiv.support_eq]
  exact hP i

/-- Homotopy equivalent complexes have the same closed homology support. -/
lemma HasHomologySupportOn.of_homotopyEquiv (hP : HasHomologySupportOn Z P)
    (e : HomotopyEquiv P Q) : HasHomologySupportOn Z Q :=
  hP.of_homologyIso (fun i ↦ e.toHomologyIso i)

/-- Isomorphic complexes have the same closed homology support. -/
lemma HasHomologySupportOn.of_iso (hP : HasHomologySupportOn Z P)
    (e : P ≅ Q) : HasHomologySupportOn Z Q :=
  hP.of_homotopyEquiv (HomotopyEquiv.ofIso e)

/-- Every integer shift preserves the closed homology support. -/
lemma HasHomologySupportOn.shift (hP : HasHomologySupportOn Z P) (n : ℤ) :
    HasHomologySupportOn Z (P⟦n⟧) := by
  intro i
  let e : (P⟦n⟧).homology i ≅ P.homology (n + i) :=
    (CochainComplex.ShiftSequence.shiftIso (ModuleCat.{u} R) n i (n + i) rfl).app P
  rw [e.toLinearEquiv.support_eq]
  exact hP (n + i)

/-- A zero complex has homology supported on every closed set. -/
lemma hasHomologySupportOn_of_isZero (hP : IsZero P) : HasHomologySupportOn Z P := by
  intro i
  have hz : IsZero (P.homology i) :=
    (HomologicalComplex.homologyFunctor _ _ i).map_isZero hP
  have : Subsingleton (P.homology i) := ModuleCat.subsingleton_of_isZero hz
  simp [Module.support_eq_empty]

/-- The long exact homology sequence preserves the closed support under mapping cones. -/
lemma HasHomologySupportOn.mappingCone (hP : HasHomologySupportOn Z P)
    (f : P ⟶ Q) (hQ : HasHomologySupportOn Z Q) :
    HasHomologySupportOn Z (CochainComplex.mappingCone f) := by
  intro i
  have he := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    (Cone.exact₃ f i (i + 1) rfl)
  exact (module_support_subset_union_of_exact _ _ he).trans
    (Set.union_subset (hQ i) (hP (i + 1)))

/-- Empty homology support is precisely acyclicity, expressed by zero homology objects. -/
lemma hasHomologySupportOn_bot_iff :
    HasHomologySupportOn (⊥ : TopologicalSpace.Closeds (PrimeSpectrum R)) P ↔
      ∀ i, IsZero (P.homology i) := by
  constructor
  · intro h i
    have hs : Module.support R (P.homology i) = ∅ := Set.eq_empty_iff_forall_notMem.mpr
      (fun p hp ↦ h i hp)
    have := Module.support_eq_empty_iff.mp hs
    exact ModuleCat.isZero_of_subsingleton _
  · intro h i
    have := ModuleCat.subsingleton_of_isZero (h i)
    simp [Module.support_eq_empty]

end SerrePositivity
