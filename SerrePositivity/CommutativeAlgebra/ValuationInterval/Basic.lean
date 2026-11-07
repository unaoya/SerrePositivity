module

public import SerrePositivity.CommutativeAlgebra.AbsolutelyIntegrallyClosed.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.FieldTheory.Perfect

/-!
概要：付値環のスペクトルに対応する区間環（BM18 Definition 4.6）。
方針：下端で商を取り、上端で局所化する。商と局所化の普遍性を一つにまとめる。
規約：区間は素イデアルの二つの端点で表し、部分区間への制限写像は逆向きに取る。
使われ方：区間の貼り合わせ、剰余体の近似、絶対整閉性と完全性。
-/

@[expose] public noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity

variable {V : Type u} [CommRing V]

/-- 下端で割った環における上端の素イデアル（BM18 Definition 4.6）。 -/
abbrev intervalPrime {a b : PrimeSpectrum V} (_ : a ≤ b) : Ideal (V ⧸ a.asIdeal) :=
  b.asIdeal.map (Ideal.Quotient.mk a.asIdeal)

instance intervalPrime_isPrime {a b : PrimeSpectrum V} (h : a ≤ b) :
    (intervalPrime h).IsPrime := by
  apply Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
  rw [Ideal.mk_ker]
  exact h

/-- スペクトルの区間に対応する環（BM18 Definition 4.6）。 -/
abbrev ValuationIntervalRing {a b : PrimeSpectrum V} (h : a ≤ b) :=
  Localization.AtPrime (intervalPrime h)

variable {a b : PrimeSpectrum V} (h : a ≤ b)

theorem intervalPrime_comap :
    (intervalPrime h).comap (Ideal.Quotient.mk a.asIdeal) = b.asIdeal := by
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr h]

theorem intervalRing_map_eq_zero {x : V} (hx : x ∈ a.asIdeal) :
    algebraMap V (ValuationIntervalRing h) x = 0 := by
  rw [IsScalarTower.algebraMap_apply V (V ⧸ a.asIdeal)]
  change (algebraMap _ (ValuationIntervalRing h)) (Ideal.Quotient.mk a.asIdeal x) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

theorem intervalRing_isUnit {x : V} (hx : x ∉ b.asIdeal) :
    IsUnit (algebraMap V (ValuationIntervalRing h) x) := by
  rw [IsScalarTower.algebraMap_apply V (V ⧸ a.asIdeal)]
  apply IsLocalization.map_units (M := (intervalPrime h).primeCompl) _ ⟨_, ?_⟩
  change Ideal.Quotient.mk a.asIdeal x ∉ intervalPrime h
  rwa [← Ideal.mem_comap, intervalPrime_comap]

variable {R : Type v} [CommRing R]

/-- 区間の環からの射の普遍性（BM18 Definition 4.6）。 -/
def intervalRingLift (f : V →+* R)
    (ha : ∀ x ∈ a.asIdeal, f x = 0) (hb : ∀ x ∉ b.asIdeal, IsUnit (f x)) :
    ValuationIntervalRing h →+* R :=
  IsLocalization.lift (M := (intervalPrime h).primeCompl)
    (g := Ideal.Quotient.lift a.asIdeal f ha) (fun y => by
      obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective y.val
      have hxb : x ∉ b.asIdeal := by
        rw [← intervalPrime_comap h]
        change Ideal.Quotient.mk a.asIdeal x ∉ intervalPrime h
        rw [hx]
        exact y.2
      simpa only [← hx, Ideal.Quotient.lift_mk] using hb x hxb)

@[simp]
theorem intervalRingLift_algebraMap (f : V →+* R) (ha hb) (x : V) :
    intervalRingLift h f ha hb (algebraMap V (ValuationIntervalRing h) x) = f x := by
  rw [IsScalarTower.algebraMap_apply V (V ⧸ a.asIdeal)]
  exact IsLocalization.lift_eq (M := (intervalPrime h).primeCompl) _ (Ideal.Quotient.mk a.asIdeal x)

theorem intervalRing_hom_ext {f g : ValuationIntervalRing h →+* R}
    (he : ∀ x, f (algebraMap V _ x) = g (algebraMap V _ x)) : f = g := by
  apply IsLocalization.ringHom_ext (intervalPrime h).primeCompl
  apply RingHom.ext
  intro x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact he y

/-- 区間の包含と逆向きの環準同型（BM18 Definition 4.6）。 -/
def intervalRingMap {c d : PrimeSpectrum V} (h' : c ≤ d) (hac : a ≤ c) (hdb : d ≤ b) :
    ValuationIntervalRing h →+* ValuationIntervalRing h' :=
  intervalRingLift h (algebraMap V _) (fun _ hx => intervalRing_map_eq_zero h' (hac hx))
    (fun _ hx => intervalRing_isUnit h' (fun hy => hx (hdb hy)))

@[simp]
theorem intervalRingMap_algebraMap {c d : PrimeSpectrum V} (h' : c ≤ d)
    (hac : a ≤ c) (hdb : d ≤ b) (x : V) :
    intervalRingMap h h' hac hdb (algebraMap V _ x) = algebraMap V _ x :=
  intervalRingLift_algebraMap h _ _ _ x

/-- 区間の環は付値環である（BM18 Definition 4.6）。 -/
theorem valuationRing_interval [IsDomain V] [ValuationRing V] :
    ValuationRing (ValuationIntervalRing h) := by
  classical
  let e := IsLocalization.orderEmbedding (intervalPrime h).primeCompl (ValuationIntervalRing h)
  let f := Ideal.comap (Ideal.Quotient.mk a.asIdeal)
  refine ValuationRing.iff_ideal_total.mpr ⟨fun I J => ?_⟩
  rcases le_total (f (e I)) (f (e J)) with he | he
  · exact Or.inl (e.le_iff_le.mp ((Ideal.comap_le_comap_iff_of_surjective _
      Ideal.Quotient.mk_surjective _ _).mp he))
  · exact Or.inr (e.le_iff_le.mp ((Ideal.comap_le_comap_iff_of_surjective _
      Ideal.Quotient.mk_surjective _ _).mp he))

/-- 絶対整閉性は区間に制限できる（BM18 Definition 4.6）。 -/
theorem aic_interval (hV : IsAbsolutelyIntegrallyClosed V) :
    IsAbsolutelyIntegrallyClosed (ValuationIntervalRing h) :=
  (hV.quotient a.asIdeal).localization (intervalPrime h).primeCompl _

/-- 絶対整閉環の素点の剰余体は代数閉体（BM18 Proposition 4.8 の証明 (3), (4)）。 -/
theorem IsAbsolutelyIntegrallyClosed.primeResidue_isAlgClosed
    (hV : IsAbsolutelyIntegrallyClosed V) (P : Ideal V) [P.IsPrime] :
    IsAlgClosed P.ResidueField :=
  ((hV.quotient P).localization (nonZeroDivisors (V ⧸ P)) P.ResidueField).isAlgClosed

/-- 完全標数 p 環の区間環は完全（BM18 Proposition 4.8 の図式 (6) の係数環）。 -/
theorem perfectRing_interval (p : ℕ) [Fact p.Prime] [PerfectRing V p]
    (hp : (p : V) = 0) : PerfectRing (ValuationIntervalRing h) p := by
  let A := V ⧸ a.asIdeal
  let H := ValuationIntervalRing h
  let M := (intervalPrime h).primeCompl
  have hpH : (p : H) = 0 := by
    rw [← map_natCast (algebraMap V H), hp, map_zero]
  let : CharP H p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hpH
  have hroot (x : A) : ∃ y : A, y ^ p = x := by
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, hy⟩ := (PerfectRing.bijective_frobenius (R := V) (p := p)).2 v
    change y ^ p = v at hy
    exact ⟨Ideal.Quotient.mk a.asIdeal y, by rw [← map_pow, hy]⟩
  apply PerfectRing.ofSurjective
  intro x
  obtain ⟨v, s, rfl⟩ := IsLocalization.exists_mk'_eq M x
  obtain ⟨r, hr⟩ := hroot v
  obtain ⟨t, ht⟩ := hroot s.val
  have htM : t ∈ M := fun he =>
    s.property (ht ▸ (intervalPrime h).pow_mem_of_mem he p (Fact.out : p.Prime).pos)
  let t' : M := ⟨t, htM⟩
  have htp : t' ^ p = s := Subtype.ext ht
  exact ⟨IsLocalization.mk' H r t', by
    rw [frobenius_def, ← IsLocalization.mk'_pow, hr, htp]⟩

/-- 絶対整閉整域は標数 p で完全である（BM18 Proposition 4.8 の付値環への帰着）。 -/
theorem IsAbsolutelyIntegrallyClosed.perfectRing_of_charP
    {A : Type u} [CommRing A] [IsDomain A] (hA : IsAbsolutelyIntegrallyClosed A)
    (p : ℕ) [Fact p.Prime] [CharP A p] : PerfectRing A p := by
  apply PerfectRing.ofSurjective
  intro x
  obtain ⟨r, hr⟩ := hA.exists_compatible_pow_roots (Fact.out : p.Prime).pos x
  exact ⟨r 1, (hr.2 0).trans hr.1⟩

end SerrePositivity
