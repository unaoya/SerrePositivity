module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Finiteness.Basic

/-! # 局所化された加群の中の有限格子

## 概要

局所化された加群の中の有限生成部分加群（格子 `IsLocalizationLattice`）と、その分母払い、テンソル積との両立を与える。

## 方針

格子の張る部分加群は Mathlib の `IsLocalization.mem_span_iff`、テンソル積との両立は `IsLocalizedModule.isBaseChange` に乗せる。

## 規約

格子は有限集合の張る部分加群として与える。

## 使われ方

KTheory の格子の類、共通模型。提出候補。
-/

@[expose] public noncomputable section

universe u

section LocalizationLatticePart

set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
namespace SerrePositivity
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
  (P : Submonoid R) [IsLocalization P B]
  {N : Type u} [AddCommGroup N] [Module R N] [Module B N] [IsScalarTower R B N]

/-- Every element becomes an element of the submodule after multiplication by a denominator. -/
def IsLocalizationLattice (L : Submodule R N) : Prop :=
  ∀ n : N, ∃ s : P, (s : R) • n ∈ L

include B in
/-- A denominator-clearing condition exhibits the inclusion as a module localization. -/
lemma IsLocalizationLattice.isLocalizedModule {L : Submodule R N}
    (h : IsLocalizationLattice P L) : IsLocalizedModule P L.subtype := by
  have hid := isLocalizedModule_id P N B
  refine ⟨fun s => hid.map_units s, ?_, ?_⟩
  · intro n
    obtain ⟨s, hs⟩ := h n
    exact ⟨(⟨(s : R) • n, hs⟩, s), rfl⟩
  · intro x y he
    exact ⟨1, by simpa using Subtype.ext he⟩

/-- Denominators can be cleared on the localized span of any set. -/
lemma isLocalizationLattice_span (t : Set N) (ht : Submodule.span B t = ⊤) :
    IsLocalizationLattice P (Submodule.span R t) := by
  intro n
  have hn : n ∈ Submodule.span B t := by rw [ht]; trivial
  induction hn using Submodule.span_induction with
  | mem n hn => exact ⟨1, by simpa using Submodule.subset_span hn⟩
  | zero => exact ⟨1, by simp⟩
  | add n m hn hm en em =>
    obtain ⟨s, hs⟩ := en
    obtain ⟨t, ht⟩ := em
    refine ⟨s * t, ?_⟩
    change ((s : R) * (t : R)) • (n + m) ∈ Submodule.span R _
    rw [smul_add]
    apply Submodule.add_mem
    · rw [mul_comm, mul_smul]
      exact Submodule.smul_mem _ _ hs
    · rw [mul_smul]
      exact Submodule.smul_mem _ _ ht
  | smul b n hn en =>
    obtain ⟨s, hs⟩ := en
    obtain ⟨⟨r, t⟩, he⟩ := IsLocalization.surj P b
    refine ⟨t * s, ?_⟩
    change ((t : R) * (s : R)) • (b • n) ∈ Submodule.span R _
    have hmul : (t : R) • (b • n) = r • n := by
      rw [← algebraMap_smul B (t : R), smul_smul, mul_comm, he, algebraMap_smul]
    rw [mul_comm, mul_smul, hmul, smul_comm]
    exact Submodule.smul_mem _ r hs

/-- Finite localized modules have finite lattices; support will be added below. -/
lemma exists_finite_lattice [Module.Finite B N] :
    ∃ L : Submodule R N, L.FG ∧ IsLocalizationLattice P L := by
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := B) (M := N)
  exact ⟨Submodule.span R (t : Set N), Submodule.fg_span t.finite_toSet,
    isLocalizationLattice_span P _ ht⟩

include B in
/-- The lattice inclusion gives the expected tensor-product identification. -/
def IsLocalizationLattice.tensorEquiv {L : Submodule R N}
    (h : IsLocalizationLattice P L) : B ⊗[R] L ≃ₗ[B] N := by
  have := h.isLocalizedModule (B := B)
  exact (IsLocalizedModule.isBaseChange P B L.subtype).equiv

end SerrePositivity

end LocalizationLatticePart
