module

public import SerrePositivity.CommutativeAlgebra.Ultraproduct.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
概要：指示冪等元による局所化としての超積（BM18 Lemma 3.25）。
方針：超フィルターに属する集合の指示冪等元を可逆化する。
規約：積環の素点に対応する超フィルターを、素点の外にある指示冪等元で定める。
使われ方：積環上の加群と余鎖複体の局所的な検査。
-/

@[expose] public noncomputable section

universe u v

open Filter Set

namespace SerrePositivity

variable {ι : Type u} (R : ι → Type v) [∀ i, CommRing (R i)]

/-- 部分集合の指示冪等元。 -/
def subsetIdempotent (s : Set ι) : ∀ i, R i := fun i => by
  classical
  exact if i ∈ s then 1 else 0

@[simp] theorem subsetIdempotent_apply_of_mem {s : Set ι} {i : ι} (h : i ∈ s) :
    subsetIdempotent R s i = 1 := by simp [subsetIdempotent, h]

@[simp] theorem subsetIdempotent_apply_of_notMem {s : Set ι} {i : ι} (h : i ∉ s) :
    subsetIdempotent R s i = 0 := by simp [subsetIdempotent, h]

@[simp] theorem subsetIdempotent_univ : subsetIdempotent R univ = 1 := by
  funext i
  simp

@[simp] theorem subsetIdempotent_empty : subsetIdempotent R ∅ = 0 := by
  funext i
  simp

theorem subsetIdempotent_inter (s t : Set ι) :
    subsetIdempotent R (s ∩ t) = subsetIdempotent R s * subsetIdempotent R t := by
  funext i
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;>
    simp [subsetIdempotent, hs, ht]

theorem subsetIdempotent_add_compl (s : Set ι) :
    subsetIdempotent R s + subsetIdempotent R sᶜ = 1 := by
  funext i
  by_cases hs : i ∈ s <;> simp [subsetIdempotent, hs]

/-- 超フィルターの集合に対応する指示冪等元からなる乗法集合（BM18 Lemma 3.25）。 -/
def ultrafilterDenominators (U : Ultrafilter ι) : Submonoid (∀ i, R i) where
  carrier := {x | ∃ s ∈ U, x = subsetIdempotent R s}
  one_mem' := ⟨univ, univ_mem, (subsetIdempotent_univ R).symm⟩
  mul_mem' := by
    rintro x y ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    exact ⟨s ∩ t, inter_mem hs ht, (subsetIdempotent_inter R s t).symm⟩

/-- 超積は指示冪等元の局所化として得られる（BM18 Lemma 3.25）。 -/
theorem isLocalization_ringUltraproduct (U : Ultrafilter ι) :
    IsLocalization (ultrafilterDenominators R U) (RingUltraproduct R U) where
  map_units := by
    rintro ⟨x, s, hs, rfl⟩
    have he : Ideal.Quotient.mk (ultraproductIdeal R U) (subsetIdempotent R s) = 1 := by
      rw [← map_one (Ideal.Quotient.mk (ultraproductIdeal R U)),
        ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      exact (show ∀ᶠ i in (U : Filter ι), i ∈ s from hs).mono (fun i hi => by
        change subsetIdempotent R s i - 1 = 0
        simp [hi])
    change IsUnit (Ideal.Quotient.mk (ultraproductIdeal R U) (subsetIdempotent R s))
    rw [he]
    exact isUnit_one
  surj z := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨(x, 1), by rw [Submonoid.coe_one, map_one, mul_one]; rfl⟩
  exists_of_eq {x y} h := by
    have he : x - y ∈ ultraproductIdeal R U := Ideal.Quotient.eq.mp h
    have hs : {i | x i = y i} ∈ U :=
      (show ∀ᶠ i in (U : Filter ι), x i - y i = 0 from he).mono
        (fun _ hi => sub_eq_zero.mp hi)
    let s : Set ι := {i | x i = y i}
    refine ⟨⟨subsetIdempotent R s, s, hs, rfl⟩, ?_⟩
    funext i
    change subsetIdempotent R s i * x i = subsetIdempotent R s i * y i
    by_cases hi : i ∈ s
    · exact congrArg (subsetIdempotent R s i * ·) hi
    · simp [hi]

/-- 素点から、そこで可逆になる指示冪等元に対応する超フィルターを取る
（BM18 Lemma 3.25 の茎による判定）。 -/
def ultrafilterOfPrime (P : PrimeSpectrum (∀ i, R i)) : Ultrafilter ι := by
  let F : Filter ι := {
    sets := {s | subsetIdempotent R s ∉ P.asIdeal}
    univ_sets := by
      change subsetIdempotent R univ ∉ P.asIdeal
      rw [subsetIdempotent_univ]
      exact fun hx => P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx isUnit_one)
    sets_of_superset := by
      intro s t hs hst ht
      apply hs
      rw [← Set.inter_eq_left.mpr hst, subsetIdempotent_inter]
      exact P.asIdeal.mul_mem_left _ ht
    inter_sets := by
      intro s t hs ht he
      have he' : subsetIdempotent R s * subsetIdempotent R t ∈ P.asIdeal := by
        rw [← subsetIdempotent_inter]
        exact he
      exact (P.isPrime.mem_or_mem he').elim hs ht }
  apply Ultrafilter.ofComplNotMemIff F
  intro s
  change ¬ (subsetIdempotent R sᶜ ∉ P.asIdeal) ↔ subsetIdempotent R s ∉ P.asIdeal
  rw [not_not]
  constructor
  · intro hs hs'
    have hone := P.asIdeal.add_mem hs' hs
    rw [subsetIdempotent_add_compl] at hone
    exact P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hone isUnit_one)
  · intro hs
    have he : subsetIdempotent R s * subsetIdempotent R sᶜ ∈ P.asIdeal := by
      rw [← subsetIdempotent_inter, Set.inter_compl_self, subsetIdempotent_empty]
      exact P.asIdeal.zero_mem
    exact (P.isPrime.mem_or_mem he).resolve_left hs

theorem ultrafilterDenominators_le_primeCompl (P : PrimeSpectrum (∀ i, R i)) :
    ultrafilterDenominators R (ultrafilterOfPrime R P) ≤ P.asIdeal.primeCompl := by
  rintro x ⟨s, hs, rfl⟩
  exact hs

end SerrePositivity
