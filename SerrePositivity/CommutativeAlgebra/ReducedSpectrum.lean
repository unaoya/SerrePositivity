module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.AlgebraicGeometry.StructureSheaf
public import Mathlib.RingTheory.Nilpotent.Basic

/-! # 被約環のスペクトルと切断

## 概要

被約環のスペクトルが有限個の商のスペクトルで互いに素に被覆されれば元の商写像の直積が同型であること、主開集合上で消える元のイデアルがスカラーの零化イデアルと一致すること、開集合上で零となる元はその開集合の全ての点で消える元と一致することを示す。

## 方針

分割は中国剰余定理、主開集合と開集合の場合は被約性から点ごとの消滅を元の消滅へ戻す。

## 規約

正則性・有限性・準コンパクト性・Noether 性は仮定しない。

## 使われ方

CLMST の命題 2.4.7 の階数の像と積（Prop247RankProductAway・Prop247AicRankImages・Prop247RankImages）。
-/

@[expose] public noncomputable section

universe u v w

section FiniteSpectrumPartitionPart

namespace SerrePositivity

/-- 被約環のスペクトルの有限商分割は、元の写像の直積を全単射にする。 -/
theorem pi_ringHom_bijective_of_spectrum_partition
    {ι : Type u} [Finite ι] (R : Type v) [CommRing R] [IsReduced R]
    (A : ι → Type w) [∀ i, CommRing (A i)] (f : ∀ i, R →+* A i)
    (hf : ∀ i, Function.Surjective (f i))
    (hdisjoint : Pairwise (fun i j => Disjoint
      (Set.range (PrimeSpectrum.comap (f i))) (Set.range (PrimeSpectrum.comap (f j)))))
    (hcover : (⋃ i, Set.range (PrimeSpectrum.comap (f i))) = Set.univ) :
    Function.Bijective (RingHom.pi f) := by
  have hcop : Pairwise (fun i j => IsCoprime (RingHom.ker (f i)) (RingHom.ker (f j))) := by
    intro i j hij
    rw [Ideal.isCoprime_iff_sup_eq]
    apply PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp
    rw [PrimeSpectrum.zeroLocus_sup,
      ← range_comap_of_surjective _ _ (hf i), ← range_comap_of_surjective _ _ (hf j)]
    exact Set.disjoint_iff_inter_eq_empty.mp (hdisjoint hij)
  constructor
  · intro a b hab
    apply sub_eq_zero.mp
    apply IsReduced.eq_zero (a - b)
    rw [nilpotent_iff_mem_prime]
    intro I hI
    have hmem : (⟨I, hI⟩ : PrimeSpectrum R) ∈
        ⋃ i, Set.range (PrimeSpectrum.comap (f i)) := by rw [hcover]; trivial
    obtain ⟨i, q, hq⟩ := Set.mem_iUnion.mp hmem
    have habi : f i a = f i b := congrFun hab i
    have hz : f i (a - b) = 0 := by
      rw [map_sub, habi, sub_self]
    have hmem' : a - b ∈ (PrimeSpectrum.comap (f i) q).asIdeal := by
      change f i (a - b) ∈ q.asIdeal
      rw [hz]
      exact q.asIdeal.zero_mem
    simpa only [hq] using hmem'
  · intro y
    let e (i : ι) := RingHom.quotientKerEquivOfSurjective (hf i)
    obtain ⟨r, hr⟩ := Ideal.pi_quotient_surjective hcop (fun i => (e i).symm (y i))
    refine ⟨r, funext (fun i => ?_)⟩
    change f i r = y i
    have hh := congrArg (e i) (hr i)
    dsimp only [e] at hh
    simpa only [RingHom.quotientKerEquivOfSurjective_apply_mk,
      RingEquiv.apply_symm_apply] using hh

end SerrePositivity

end FiniteSpectrumPartitionPart

section ReducedPrincipalVanishingPart

namespace SerrePositivity

/-- In a reduced ring the ideal vanishing on D(d) is Ann(d). -/
theorem vanishingIdeal_basicOpen_eq_annihilator
    (R : Type u) [CommRing R] [IsReduced R] (d : R) :
    PrimeSpectrum.vanishingIdeal (PrimeSpectrum.basicOpen d : Set (PrimeSpectrum R)) =
      (Ideal.span {d}).annihilator := by
  ext x
  rw [PrimeSpectrum.mem_vanishingIdeal, Submodule.mem_annihilator_span_singleton]
  change (∀ P : PrimeSpectrum R, d ∉ P.asIdeal → x ∈ P.asIdeal) ↔ x * d = 0
  constructor
  · intro hx
    have hn : x * d ∈ nilradical R := by
      rw [PrimeSpectrum.nilradical_eq_iInf, Submodule.mem_iInf]
      intro P
      by_cases hd : d ∈ P.asIdeal
      · exact P.asIdeal.mul_mem_left x hd
      · exact P.asIdeal.mul_mem_right d (hx P hd)
    exact (mem_nilradical.mp hn).eq_zero
  · intro hx P hd
    exact (P.isPrime.mem_or_mem (hx ▸ P.asIdeal.zero_mem)).resolve_right hd

end SerrePositivity

end ReducedPrincipalVanishingPart

section ReducedSectionImagePart

namespace SerrePositivity
open TopologicalSpace Opposite
open AlgebraicGeometry

/-- 被約環では、構造層の開集合上の切断への写像の核はその開集合の消滅イデアルである。 -/
theorem ker_algebraMap_sections_eq_vanishingIdeal
    (R : Type u) [CommRing R] [IsReduced R] (U : Opens (PrimeSpectrum R)) :
    RingHom.ker (algebraMap R ((Spec.structureSheaf R).obj.obj (op U))) =
      PrimeSpectrum.vanishingIdeal (U : Set (PrimeSpectrum R)) := by
  ext f
  change algebraMap R ((Spec.structureSheaf R).obj.obj (op U)) f = 0 ↔ _
  rw [PrimeSpectrum.mem_vanishingIdeal]
  constructor
  · intro h x hx
    have hz := congrArg (fun s => s.1 ⟨x, hx⟩) h
    change LocalizedModule.mkLinearMap x.asIdeal.primeCompl R f = 0 at hz
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff x.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap x.asIdeal.primeCompl R)).mp hz
    have hsf : (s : R) * f = 0 := hs
    exact (x.2.mem_or_mem (hsf ▸ x.asIdeal.zero_mem)).resolve_left s.property
  · intro h
    apply Subtype.ext
    funext x
    change LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl R f = 0
    obtain ⟨_, ⟨_, ⟨b, rfl⟩, rfl⟩, hbx, hbU⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open x.2 U.2
    have hnil : IsNilpotent (b * f) := by
      apply (PrimeSpectrum.basicOpen_eq_bot_iff _).mp
      apply le_antisymm ?_ bot_le
      intro y hy
      rw [PrimeSpectrum.basicOpen_mul] at hy
      exact False.elim (hy.2 (h y (hbU hy.1)))
    apply (IsLocalizedModule.eq_zero_iff x.1.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl R)).mpr
    refine ⟨⟨b, hbx⟩, ?_⟩
    exact IsReduced.eq_zero (b * f) hnil

end SerrePositivity

end ReducedSectionImagePart

section KernelOfReducedPart

namespace SerrePositivity

/-- 被約環への写像の核は、生成イデアルに冪が属するすべての元を含む。 -/
theorem mem_kernel_comp_quotient_of_pow_mem_span
    {R C : Type u} [CommRing R] [CommRing C] [IsReduced C]
    (g : R) (f : R ⧸ Ideal.span {g} →+* C) (x : R) (k : ℕ)
    (hx : x ^ k ∈ Ideal.span {g}) :
    x ∈ RingHom.ker (f.comp (Ideal.Quotient.mk (Ideal.span {g}))) := by
  change f (Ideal.Quotient.mk (Ideal.span {g}) x) = 0
  apply IsReduced.eq_zero
  refine ⟨k, ?_⟩
  rw [← map_pow, ← map_pow, Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

end SerrePositivity

end KernelOfReducedPart
