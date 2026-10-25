module

public import SerrePositivity.BhattScholze.Delta.Division.Relations.DeltaDivisionIteratedRelations
public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeFiniteResidue

/-! # δ除算関係式の有限深さの通常剰余

商イデアルのδ安定性を仮定せず、源のδ計算と通常環射で最初の冪方程式を得る。
-/

@[expose] public noncomputable section
universe u v w
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {B : Type v} [CommRing B]

/-- 元が消える通常射の下で、δは符号を保つ。 -/
theorem DeltaStructure.map_delta_neg_of_zero (D : DeltaStructure p A) (q : A →+* B)
    (x : A) (hx : q x = 0) : q (D.delta (-x)) = -q (D.delta x) := by
  have h := D.map_delta_add_of_left_zero q x (-x) hx
  rw [add_neg_cancel, D.delta_zero, map_zero] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- 左項を消す通常射の下でのδ差公式。 -/
theorem DeltaStructure.map_delta_sub_of_both_zero (D : DeltaStructure p A) (q : A →+* B)
    (x y : A) (hx : q x = 0) (hy : q y = 0) :
    q (D.delta (x - y)) = q (D.delta x) - q (D.delta y) := by
  rw [sub_eq_add_neg, D.map_delta_add_of_left_zero q x (-y) hx,
    D.map_delta_neg_of_zero q y hy, sub_eq_add_neg]

/-- 関係式とその最初のδ像を消す通常射の下での初期冪方程式。
源でd*x=aを仮定せず、商のδ構造も仮定しない。 -/
theorem deltaDivisionFirstRelation_pow_of_vanishing
    (D : DeltaStructure p A) (q : A →+* B) (d x a : A)
    (hp : q (p : A) = 0) (hd : q d = 0)
    (h0 : q (d * x - a) = 0) (h1 : q (D.delta (d * x - a)) = 0)
    (u : Bˣ) (hu : (u : B) = q (D.delta d)) :
    (q x) ^ p = (u⁻¹ : Bˣ) * q (D.delta a) := by
  have hdx : q (d * x) = 0 := by rw [map_mul, hd, zero_mul]
  have ha : q a = 0 := by
    rw [map_sub, hdx, zero_sub, neg_eq_zero] at h0
    exact h0
  rw [D.map_delta_sub_of_both_zero q (d * x) a hdx ha, sub_eq_zero] at h1
  rw [D.map_delta_mul_of_prime_zero q hp d x, hd,
    zero_pow (Fact.out : p.Prime).ne_zero, zero_mul, zero_add, ← hu] at h1
  calc
    (q x) ^ p = ((u⁻¹ : Bˣ) * (u : B)) * (q x) ^ p := by simp
    _ = (u⁻¹ : Bˣ) * q (D.delta a) := by rw [mul_assoc, h1]

/-- p,d,aを消す通常射の下で、最初のδ関係式は具体的な冪多項式となる。 -/
theorem deltaDivisionFirstRelation_delta_image
    (D : DeltaStructure p A) (q : A →+* B) (d x a : A)
    (hp : q (p : A) = 0) (hd : q d = 0) (ha : q a = 0) :
    q (D.delta (d * x - a)) = q (D.delta d) * (q x) ^ p - q (D.delta a) := by
  have hdx : q (d * x) = 0 := by rw [map_mul, hd, zero_mul]
  rw [D.map_delta_sub_of_both_zero q (d * x) a hdx ha,
    D.map_delta_mul_of_prime_zero q hp d x, hd,
    zero_pow (Fact.out : p.Prime).ne_zero, zero_mul, zero_add]

/-- p,dを消す通常射について、低次の関係式の消滅とモニック表示は同値。 -/
theorem deltaDivisionFirstRelations_vanish_iff
    (D : DeltaStructure p A) (q : A →+* B) (d x a : A)
    (hp : q (p : A) = 0) (hd : q d = 0)
    (u : Bˣ) (hu : (u : B) = q (D.delta d)) :
    (q (d * x - a) = 0 ∧ q (D.delta (d * x - a)) = 0) ↔
      (q a = 0 ∧ (q x) ^ p = (u⁻¹ : Bˣ) * q (D.delta a)) := by
  constructor
  · rintro ⟨h0, h1⟩
    have ha : q a = 0 := by
      simpa only [map_sub, map_mul, hd, zero_mul, zero_sub, neg_eq_zero] using h0
    exact ⟨ha, deltaDivisionFirstRelation_pow_of_vanishing D q d x a hp hd h0 h1 u hu⟩
  · rintro ⟨ha, hpow⟩
    constructor
    · rw [map_sub, map_mul, hd, ha, zero_mul, sub_self]
    · rw [deltaDivisionFirstRelation_delta_image D q d x a hp hd ha, ← hu, hpow,
        ← mul_assoc, Units.mul_inv, one_mul, sub_self]

variable {σ : Type w}

/-- 相対自由δ環で、深さ0,1の関係式の消滅から初期変数の冪方程式を得る。 -/
theorem deltaDivisionFiniteFirstRoot_pow
    (D : DeltaStructure p A) (d : A) (a : σ → A)
    (q : RelativeFreeDeltaRing (R := A) σ →+* B)
    (hp : q (p : RelativeFreeDeltaRing (R := A) σ) = 0)
    (hd : q (MvPolynomial.C d) = 0)
    (hrel : ∀ s n, n ≤ 1 → q (deltaDivisionIteratedRelation D d a s n) = 0)
    (u : Bˣ) (hu : (u : B) = q (MvPolynomial.C (D.delta d))) (s : σ) :
    (q (MvPolynomial.X (s, 0))) ^ p = (u⁻¹ : Bˣ) * q (MvPolynomial.C (D.delta (a s))) := by
  have h := deltaDivisionFirstRelation_pow_of_vanishing (relativeFreeDeltaStructure σ D)
    q (MvPolynomial.C d) (MvPolynomial.X (s, 0)) (MvPolynomial.C (a s))
    hp hd (hrel s 0 (by decide)) (hrel s 1 le_rfl) u
    (by simpa only [relativeFreeDeltaStructure_delta_C] using hu)
  simpa only [relativeFreeDeltaStructure_delta_C] using h

/-- p,dと深さ1以下の関係式を課す通常イデアル。δ安定性は要求しない。 -/
def deltaDivisionFirstResidueIdeal (D : DeltaStructure p A) (d : A) (a : σ → A) :
    Ideal (RelativeFreeDeltaRing (R := A) σ) :=
  Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ⊔
    deltaDivisionFiniteRelationIdeal D d a 1

/-- 実際の有限深さの通常商で初期変数が満たす冪方程式。
δ除算包全体の商に進む前に成立する。 -/
theorem deltaDivisionFirstResidueQuotient_root_pow
    (D : DeltaStructure p A) (d : A) (a : σ → A)
    (u : Aˣ) (hu : (u : A) = D.delta d) (s : σ) :
    let q := Ideal.Quotient.mk (deltaDivisionFirstResidueIdeal D d a)
    (q (MvPolynomial.X (s, 0))) ^ p = q (MvPolynomial.C ((u⁻¹ : Aˣ) * D.delta (a s))) := by
  let J := deltaDivisionFirstResidueIdeal D d a
  let q := Ideal.Quotient.mk J
  let f := q.comp (MvPolynomial.C : A →+* RelativeFreeDeltaRing (R := A) σ)
  have hp : q (p : RelativeFreeDeltaRing (R := A) σ) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact (show Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ≤ J
      from le_sup_left) (Ideal.subset_span (by simp))
  have hd : q (MvPolynomial.C d) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact (show Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ≤ J
      from le_sup_left) (Ideal.subset_span (by simp))
  have hrel : ∀ t n, n ≤ 1 → q (deltaDivisionIteratedRelation D d a t n) = 0 := by
    intro t n hn
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply (show deltaDivisionFiniteRelationIdeal D d a 1 ≤ J from le_sup_right)
    exact Ideal.subset_span (Set.mem_range.mpr ⟨(t, ⟨n, Nat.lt_succ_of_le hn⟩), rfl⟩)
  have hunit : ((u.map f : (RelativeFreeDeltaRing (R := A) σ ⧸ J)ˣ) :
      RelativeFreeDeltaRing (R := A) σ ⧸ J) = q (MvPolynomial.C (D.delta d)) := by
    change f (u : A) = _
    rw [hu]
    rfl
  have h := deltaDivisionFiniteFirstRoot_pow D d a q hp hd hrel (u.map f) hunit s
  change _ = f ((u⁻¹ : Aˣ) * D.delta (a s))
  rw [map_mul]
  exact h

end SerrePositivity.BhattScholze
