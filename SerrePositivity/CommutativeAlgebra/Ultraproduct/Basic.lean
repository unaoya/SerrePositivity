module

public import SerrePositivity.CommutativeAlgebra.ValuationInterval.Basic
public import Mathlib.Order.Filter.Ultrafilter.Defs
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.Localization.Basic

/-!
概要：絶対整閉付値環の超積（BM18 Lemma 3.27、BS17 Lemma 6.2 の証明）。
方針：超フィルター上で零になる元で割り、付値環の整除の全順序と絶対整閉性を移す。
規約：絶対整閉性は正次数のモニック多項式で述べる。
使われ方：完全環の v 被覆の積を絶対整閉付値環の族で検査する。
-/

@[expose] public noncomputable section

universe u v

open Filter Polynomial

namespace SerrePositivity

variable {ι : Type u} (R : ι → Type v) [∀ i, CommRing (R i)]

/-- 超フィルターに関して零である元のイデアル（BM18 Lemma 3.27）。 -/
def ultraproductIdeal (U : Ultrafilter ι) : Ideal (∀ i, R i) where
  carrier := {x | ∀ᶠ i in (U : Filter ι), x i = 0}
  zero_mem' := Eventually.of_forall (fun _ => rfl)
  add_mem' hx hy := (hx.and hy).mono (fun i hi => by
    change _ + _ = (0 : R i)
    rw [hi.1, hi.2, add_zero])
  smul_mem' a b hb := hb.mono (fun i hi => by
    change a i * b i = 0
    rw [hi, mul_zero])

/-- 可換環の超積（BM18 Lemma 3.27）。 -/
abbrev RingUltraproduct (U : Ultrafilter ι) := (∀ i, R i) ⧸ ultraproductIdeal R U

theorem ultraproductIdeal_isPrime (U : Ultrafilter ι) [∀ i, IsDomain (R i)] :
    (ultraproductIdeal R U).IsPrime := by
  refine ⟨?_, ?_⟩
  · intro h
    have he : (1 : ∀ i, R i) ∈ ultraproductIdeal R U := by simp [h]
    change ∀ᶠ i in (U : Filter ι), (1 : R i) = 0 at he
    obtain ⟨i, hi⟩ := he.exists
    exact one_ne_zero hi
  · intro x y h
    have he : ∀ᶠ i in (U : Filter ι), x i = 0 ∨ y i = 0 :=
      (show ∀ᶠ i in (U : Filter ι), x i * y i = 0 from h).mono
        (fun _ hi => mul_eq_zero.mp hi)
    exact Ultrafilter.eventually_or.mp he

instance (U : Ultrafilter ι) [∀ i, IsDomain (R i)] : IsDomain (RingUltraproduct R U) := by
  let := ultraproductIdeal_isPrime R U
  infer_instance

/-- 付値環の超積は付値環（BM18 Lemma 3.27）。 -/
theorem valuationRing_ultraproduct (U : Ultrafilter ι) [∀ i, IsDomain (R i)]
    [∀ i, ValuationRing (R i)] : ValuationRing (RingUltraproduct R U) := by
  classical
  refine ValuationRing.iff_dvd_total.mpr ⟨fun a b => ?_⟩
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
  have he : (∀ᶠ i in (U : Filter ι), x i ∣ y i) ∨ ∀ᶠ i in (U : Filter ι), y i ∣ x i :=
    Ultrafilter.eventually_or.mp
      (Eventually.of_forall (fun i => ValuationRing.dvd_total (x i) (y i)))
  have lift (x y : ∀ i, R i) (hxy : ∀ᶠ i in (U : Filter ι), x i ∣ y i) :
      Ideal.Quotient.mk (ultraproductIdeal R U) x ∣
        Ideal.Quotient.mk (ultraproductIdeal R U) y := by
    let z (i : ι) : R i := if h : x i ∣ y i then Classical.choose h else 0
    refine ⟨Ideal.Quotient.mk _ z, ?_⟩
    rw [← map_mul, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact hxy.mono (fun i hi => by
      change y i - x i * z i = 0
      rw [sub_eq_zero, show z i = Classical.choose hi by simp [z, hi]]
      exact Classical.choose_spec hi)
  exact he.imp (lift x y) (lift y x)

/-- 絶対整閉環の直積は絶対整閉。 -/
theorem aic_pi [∀ i, Nontrivial (R i)] (hR : ∀ i, IsAbsolutelyIntegrallyClosed (R i)) :
    IsAbsolutelyIntegrallyClosed (∀ i, R i) := by
  intro P hP hd
  let e (i : ι) : (∀ i, R i) →+* R i := Pi.evalRingHom R i
  have root (i : ι) : ∃ x, (P.map (e i)).IsRoot x :=
    hR i _ (hP.map _) (by rw [hP.natDegree_map]; exact hd)
  choose x hx using root
  refine ⟨x, ?_⟩
  change P.eval x = 0
  funext i
  change (e i) (P.eval x) = 0
  rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map]
  exact hx i

/-- 絶対整閉付値環の超積は絶対整閉（BM18 Lemma 3.27）。 -/
theorem aic_ultraproduct (U : Ultrafilter ι) [∀ i, IsDomain (R i)]
    (hR : ∀ i, IsAbsolutelyIntegrallyClosed (R i)) :
    IsAbsolutelyIntegrallyClosed (RingUltraproduct R U) :=
  (aic_pi R hR).quotient _

/-- 標数 p の絶対整閉付値環の超積は完全（BM18 Lemma 3.27 の完全環への適用）。 -/
theorem perfectRing_ultraproduct_of_aic (U : Ultrafilter ι) [∀ i, IsDomain (R i)]
    (hR : ∀ i, IsAbsolutelyIntegrallyClosed (R i)) (p : ℕ) [Fact p.Prime]
    (hp : (p : ∀ i, R i) = 0) : PerfectRing (RingUltraproduct R U) p := by
  have hq : (p : RingUltraproduct R U) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (ultraproductIdeal R U)), hp, map_zero]
  let : CharP (RingUltraproduct R U) p :=
    (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hq
  exact (aic_ultraproduct R U hR).perfectRing_of_charP p

end SerrePositivity
