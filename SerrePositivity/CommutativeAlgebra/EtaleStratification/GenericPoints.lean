module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.Tactic.Ring
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# 一般点の剰余体積と全商環

## 概要
被約 noetherian 環の全商環を、極小点の剰余体の有限積として記述する。

## 方針
極小素イデアルを分離する元を選び、各成分の分数表示から一つの共通分母を作る。

## 規約
構造射は各剰余体への標準射を成分とする。

## 使われ方
有限エタール層別の一般点での分解。
-/

@[expose] public section
noncomputable section
universe u

namespace SerrePositivity.CommutativeAlgebra

/-- 全商環の因子は基底の極小点で添字づける。 -/
abbrev GenericPoint (R : Type u) [CommRing R] :=
  {P : PrimeSpectrum R // P.asIdeal ∈ minimalPrimes R}

abbrev GenericField {R : Type u} [CommRing R] (P : GenericPoint R) := P.val.asIdeal.ResidueField
abbrev GenericProduct (R : Type u) [CommRing R] := ∀ P : GenericPoint R, GenericField P

def genericProductMap (R : Type u) [CommRing R] : R →+* GenericProduct R :=
  RingHom.pi (fun P => algebraMap R (GenericField P))

/-- Noetherian 環の極小点は有限。剰余体の積を有限積として扱うための補題。 -/
theorem finite_genericPoint (R : Type u) [CommRing R] [IsNoetherianRing R] :
    Finite (GenericPoint R) := by
  let : Finite {I : Ideal R // I ∈ minimalPrimes R} :=
    (minimalPrimes.finite_of_isNoetherianRing R).to_subtype
  apply Finite.of_injective
    (fun P : GenericPoint R ↦ (⟨P.val.asIdeal, P.property⟩ :
      {I : Ideal R // I ∈ minimalPrimes R}))
  intro P Q h
  apply Subtype.ext
  apply PrimeSpectrum.ext
  exact congrArg Subtype.val h

/-- 被約環の元が全極小点で零なら、その元は零。 -/
private theorem eq_zero_of_genericField_eq_zero {R : Type u} [CommRing R] [IsReduced R]
    (x : R) (hx : ∀ P : GenericPoint R, algebraMap R (GenericField P) x = 0) : x = 0 := by
  have hnil : x ∈ nilradical R := by
    change x ∈ (⊥ : Ideal R).radical
    rw [← Ideal.sInf_minimalPrimes, Submodule.mem_sInf]
    intro I hI
    let : Ideal.IsPrime I := hI.isPrime
    exact (Ideal.algebraMap_residueField_eq_zero (I := I)).mp (hx ⟨⟨I, hI.isPrime⟩, hI⟩)
  exact (mem_nilradical.mp hnil).eq_zero

/-- 各極小点を他の極小点から分離する元。 -/
private theorem exists_genericPoint_separator {R : Type u} [CommRing R]
    [IsNoetherianRing R] (P : GenericPoint R) :
    ∃ s : R, s ∉ P.val.asIdeal ∧ ∀ Q : GenericPoint R, Q ≠ P → s ∈ Q.val.asIdeal := by
  classical
  let : Finite (GenericPoint R) := finite_genericPoint R
  let : Fintype (GenericPoint R) := Fintype.ofFinite _
  let J := (Finset.univ.erase P).inf fun Q : GenericPoint R ↦ Q.val.asIdeal
  have hn : ¬ J ≤ P.val.asIdeal := by
    intro h
    obtain ⟨Q, hQ, hQP⟩ := P.val.isPrime.inf_le'.mp h
    have hpq : P.val.asIdeal ≤ Q.val.asIdeal := P.property.2 ⟨Q.val.isPrime, bot_le⟩ hQP
    have he : Q = P := Subtype.ext (PrimeSpectrum.ext (le_antisymm hQP hpq))
    exact (Finset.mem_erase.mp hQ).1 he
  obtain ⟨s, hs, hsp⟩ := IsConcreteLE.not_le_iff_exists.mp hn
  refine ⟨s, hsp, fun Q hQ ↦ ?_⟩
  exact (show J ≤ Q.val.asIdeal from
    Finset.inf_le (Finset.mem_erase.mpr ⟨hQ, Finset.mem_univ Q⟩)) hs

/-- どの極小点にも含まれないイデアルには、全極小点を避ける元がある。 -/
theorem exists_mem_ideal_avoiding_genericPoints {R : Type u} [CommRing R]
    [IsNoetherianRing R] (I : Ideal R) (hI : ∀ P : GenericPoint R, ¬ I ≤ P.val.asIdeal) :
    ∃ g ∈ I, ∀ P : GenericPoint R, g ∉ P.val.asIdeal := by
  classical
  let : Finite (GenericPoint R) := finite_genericPoint R
  by_cases h : Nonempty (GenericPoint R)
  · obtain ⟨P⟩ := h
    have hn : ¬ (I : Set R) ⊆ ⋃ Q : GenericPoint R, ⋃ _ : Q ∈ (Set.univ : Set (GenericPoint R)),
        (Q.val.asIdeal : Set R) := by
      intro h
      obtain ⟨Q, _, hQ⟩ := (Ideal.subset_union_prime_finite Set.finite_univ P P
        (fun Q _ _ _ ↦ Q.val.isPrime)).mp h
      exact hI Q hQ
    obtain ⟨g, hg, hn⟩ := Set.not_subset.mp hn
    exact ⟨g, hg, fun Q hQ ↦ hn (Set.mem_iUnion.mpr
      ⟨Q, Set.mem_iUnion.mpr ⟨Set.mem_univ Q, hQ⟩⟩)⟩
  · exact ⟨0, I.zero_mem, fun P ↦ False.elim (h ⟨P⟩)⟩

/-- 全極小点を含む開集合の中に、全極小点を含む主開集合を選べる。 -/
theorem exists_basicOpen_around_genericPoints {R : Type u} [CommRing R]
    [IsNoetherianRing R] (U : Set (PrimeSpectrum R)) (hU : IsOpen U)
    (hgeneric : ∀ P : GenericPoint R, P.val ∈ U) :
    ∃ g : R, (∀ P : GenericPoint R, g ∉ P.val.asIdeal) ∧
      (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)) ⊆ U := by
  let I := PrimeSpectrum.vanishingIdeal Uᶜ
  have hclosed : PrimeSpectrum.zeroLocus (I : Set R) = Uᶜ := by
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hU.isClosed_compl.closure_eq]
  have hI (P : GenericPoint R) : ¬ I ≤ P.val.asIdeal := by
    intro h
    have hm : P.val ∈ PrimeSpectrum.zeroLocus (I : Set R) := h
    rw [hclosed] at hm
    exact hm (hgeneric P)
  obtain ⟨g, hg, havoid⟩ := exists_mem_ideal_avoiding_genericPoints I hI
  refine ⟨g, havoid, ?_⟩
  intro P hP
  by_contra hn
  have hm : P ∈ PrimeSpectrum.zeroLocus (I : Set R) := hclosed.symm ▸ hn
  exact hP (hm hg)

/-- 剰余体の元を元の環の元の比で表す。 -/
private theorem exists_genericField_fraction {R : Type u} [CommRing R]
    (P : GenericPoint R) (x : GenericField P) :
    ∃ a b : R, algebraMap R (GenericField P) b ≠ 0 ∧
      algebraMap R (GenericField P) a / algebraMap R (GenericField P) b = x := by
  obtain ⟨a, b, hb, hx⟩ := IsFractionRing.div_surjective (R ⧸ P.val.asIdeal) x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  refine ⟨a, b, ?_, hx⟩
  change algebraMap (R ⧸ P.val.asIdeal) (GenericField P)
    (Ideal.Quotient.mk P.val.asIdeal b) ≠ 0
  exact fun h ↦ nonZeroDivisors.ne_zero hb
    (IsFractionRing.injective (R ⧸ P.val.asIdeal) (GenericField P)
      (h.trans (map_zero _).symm))

/-- 被約 noetherian 環の全商環は、極小点の剰余体の積。 -/
theorem isLocalization_genericProduct (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsReduced R] :
    letI : Algebra R (GenericProduct R) := (genericProductMap R).toAlgebra
    IsLocalization (nonZeroDivisors R) (GenericProduct R) := by
  classical
  let : Algebra R (GenericProduct R) := (genericProductMap R).toAlgebra
  let : Finite (GenericPoint R) := finite_genericPoint R
  let : Fintype (GenericPoint R) := Fintype.ofFinite _
  have hregular (r : R) (hr : ∀ P : GenericPoint R, algebraMap R (GenericField P) r ≠ 0) :
      r ∈ nonZeroDivisors R := by
    rw [mem_nonZeroDivisors_iff_left]
    intro x hx
    apply eq_zero_of_genericField_eq_zero x
    intro P
    have he := congrArg (algebraMap R (GenericField P)) hx
    simpa only [map_mul, map_zero, mul_eq_zero, hr P, false_or] using he
  refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
  · intro r
    apply Pi.isUnit_iff.mpr
    intro P
    apply isUnit_iff_ne_zero.mpr
    change algebraMap R (GenericField P) r ≠ 0
    intro he
    exact notMem_nonZeroDivisors_of_mem_mem_minimalPrimes
      ((Ideal.algebraMap_residueField_eq_zero (I := P.val.asIdeal)).mp he) P.property r.property
  · intro x
    choose a b hb hx using fun P : GenericPoint R ↦ exists_genericField_fraction P (x P)
    choose s hs hsep using fun P : GenericPoint R ↦ exists_genericPoint_separator P
    have hsum (t : GenericPoint R → R) (P : GenericPoint R) :
        algebraMap R (GenericField P) (∑ Q, s Q * t Q) =
          algebraMap R (GenericField P) (s P * t P) := by
      rw [map_sum]
      apply Finset.sum_eq_single P
      · intro Q _ hQP
        rw [map_mul, (Ideal.algebraMap_residueField_eq_zero (I := P.val.asIdeal)).mpr
          (hsep Q P hQP.symm), zero_mul]
      · simp
    let d := ∑ P, s P * b P
    have hd : d ∈ nonZeroDivisors R := hregular d fun P ↦ by
      rw [hsum, map_mul]
      exact mul_ne_zero (fun h ↦ hs P
        ((Ideal.algebraMap_residueField_eq_zero (I := P.val.asIdeal)).mp h)) (hb P)
    refine ⟨⟨∑ P, s P * a P, ⟨d, hd⟩⟩, ?_⟩
    ext P
    change x P * algebraMap R (GenericField P) d =
      algebraMap R (GenericField P) (∑ Q, s Q * a Q)
    rw [hsum, hsum, map_mul, map_mul]
    calc
      x P * (algebraMap R (GenericField P) (s P) * algebraMap R (GenericField P) (b P)) =
          algebraMap R (GenericField P) (s P) *
            (x P * algebraMap R (GenericField P) (b P)) := by ring
      _ = _ := by rw [← (div_eq_iff (hb P)).mp (hx P)]
  · intro x y h
    have he : x - y = 0 := eq_zero_of_genericField_eq_zero (x - y) fun P ↦ by
      rw [map_sub]
      exact sub_eq_zero.mpr (congrFun h P)
    exact ⟨1, by simpa using sub_eq_zero.mp he⟩

end SerrePositivity.CommutativeAlgebra
