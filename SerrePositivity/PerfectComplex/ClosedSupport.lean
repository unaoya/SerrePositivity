module

public import SerrePositivity.PerfectComplex.Support
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

end SerrePositivity
