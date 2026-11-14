module

public import SerrePositivity.BhattScholze.Delta.Division.Relations
public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeFiniteResidue
public import SerrePositivity.BhattScholze.Delta.Division.Basic
public import Mathlib.Algebra.Polynomial.Monic
public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeDelta
public import Mathlib.RingTheory.Polynomial.Quotient
public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeFiniteDelta

/-!
# δ 除算関係式の (p,d) 剰余とモニック方程式

## 概要
δ 除算関係式の有限深さの通常剰余と、(p,d) 剰余で現れる最初・二段目のモニック方程式、最初の剰余と第 2 有限段の剰余のモニック関係式表示・後続変数の多項式表示・関係式消滅の逆向き比較。
BS 著者版 Corollary 2.39 と Proposition 3.13 の包の計算に使う、δ 関係式の剰余を求める。

## 方針
構成ごとに補題をまとめ、各節で共通の仮定を明示する。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`Andre/Envelope/JetRegularity`、`Andre/Envelope/Normalized`、`Andre/Envelope/PDivision`、`Delta/Division/Witt`。
-/

universe u v w

/-! ## δ除算関係式の有限深さの通常剰余

商イデアルのδ安定性を仮定せず、源のδ計算と通常環射で最初の冪方程式を得る。
-/

@[expose] public noncomputable section DeltaDivisionFiniteResidueRelation

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

end DeltaDivisionFiniteResidueRelation

/-! ## δ除算関係式の(p,d)剰余の最初のモニック方程式

d*x=aをδで微分し、p,dを消す通常の環射に沿って計算する。
剰余環にδ構造を要求せず、一般pねじれ・零終域も含む。
この最初の方程式だけから除算包全体の平坦性を結論しない。
-/

@[expose] public noncomputable section DeltaDivisionResidueRelation

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {B : Type v} [CommRing B]

/-- p,dを消す射の下で、d*x=aのδ関係式はδ(d)*x^p=δ(a)となる。 -/
theorem delta_mul_relation_residue (D : DeltaStructure p A) (d x a : A)
    (h : d * x = a) (q : A →+* B) (hp : q (p : A) = 0) (hd : q d = 0) :
    q (D.delta d) * (q x) ^ p = q (D.delta a) := by
  have he := congrArg (fun z ↦ q (D.delta z)) h
  rw [D.delta_mul] at he
  simpa only [map_add, map_mul, map_pow, hd, hp,
    zero_pow (Fact.out : p.Prime).ne_zero, zero_mul, zero_add, add_zero] using he

/-- δ(d)の像を表す単元を指定すれば、最初の関係式をモニックな冪方程式に直せる。 -/
theorem delta_mul_relation_residue_pow (D : DeltaStructure p A) (d x a : A)
    (h : d * x = a) (q : A →+* B) (hp : q (p : A) = 0) (hd : q d = 0)
    (u : Bˣ) (hu : (u : B) = q (D.delta d)) :
    (q x) ^ p = (u⁻¹ : Bˣ) * q (D.delta a) := by
  have he := delta_mul_relation_residue D d x a h q hp hd
  rw [← hu] at he
  calc
    (q x) ^ p = ((u⁻¹ : Bˣ) * (u : B)) * (q x) ^ p := by simp
    _ = (u⁻¹ : Bˣ) * q (D.delta a) := by rw [mul_assoc, he]

/-- 実際のδ添加環の初期変数は、(p,d)剰余で具体的な冪方程式を満たす。 -/
theorem deltaAdjoinDivision_variable_pow_residue {σ : Type w}
    (D : DeltaStructure p A) (d : A) (a : σ → A)
    (q : DeltaAdjoinDivision D d a →+* B)
    (hp : q (p : DeltaAdjoinDivision D d a) = 0)
    (hd : q (deltaAdjoinDivisionMap D d a d) = 0)
    (u : Bˣ) (hu : (u : B) = q (deltaAdjoinDivisionMap D d a (D.delta d))) (s : σ) :
    (q (deltaAdjoinDivisionVariable D d a s)) ^ p =
      (u⁻¹ : Bˣ) * q (deltaAdjoinDivisionMap D d a (D.delta (a s))) := by
  have hmap := deltaAdjoinDivisionMap_isDeltaHom D d a
  have hu' : (u : B) = q ((deltaAdjoinDivisionStructure D d a).delta
      (deltaAdjoinDivisionMap D d a d)) := by rw [← hmap d]; exact hu
  have he := delta_mul_relation_residue_pow (deltaAdjoinDivisionStructure D d a)
    (deltaAdjoinDivisionMap D d a d) (deltaAdjoinDivisionVariable D d a s)
    (deltaAdjoinDivisionMap D d a (a s)) (deltaAdjoinDivision_relation D d a s)
    q hp hd u hu'
  rw [← hmap (a s)] at he
  exact he

/-- 初期変数の方程式は、係数を明示した次数pのモニック多項式である。 -/
theorem deltaAdjoinDivision_variable_monic_root_residue {σ : Type w}
    (D : DeltaStructure p A) (d : A) (a : σ → A)
    (q : DeltaAdjoinDivision D d a →+* B)
    (hp : q (p : DeltaAdjoinDivision D d a) = 0)
    (hd : q (deltaAdjoinDivisionMap D d a d) = 0)
    (u : Bˣ) (hu : (u : B) = q (deltaAdjoinDivisionMap D d a (D.delta d))) (s : σ) :
    (Polynomial.X ^ p - Polynomial.C
      ((u⁻¹ : Bˣ) * q (deltaAdjoinDivisionMap D d a (D.delta (a s))))).Monic ∧
    Polynomial.IsRoot (Polynomial.X ^ p - Polynomial.C
      ((u⁻¹ : Bˣ) * q (deltaAdjoinDivisionMap D d a (D.delta (a s)))))
      (q (deltaAdjoinDivisionVariable D d a s)) := by
  constructor
  · exact Polynomial.monic_X_pow_sub_C _ (Fact.out : p.Prime).ne_zero
  · change Polynomial.eval _ _ = 0
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      deltaAdjoinDivision_variable_pow_residue D d a q hp hd u hu s, sub_self]

/-- distinguished dなら、モニック方程式の係数の単元を実際に供給できる。 -/
theorem exists_deltaAdjoinDivision_variable_monic_root_residue {σ : Type w}
    (D : DeltaStructure p A) (d : A) (a : σ → A) (hdist : D.IsDistinguished d)
    (q : DeltaAdjoinDivision D d a →+* B)
    (hp : q (p : DeltaAdjoinDivision D d a) = 0)
    (hd : q (deltaAdjoinDivisionMap D d a d) = 0) :
    ∃ u : Bˣ, (u : B) = q (deltaAdjoinDivisionMap D d a (D.delta d)) ∧
      ∀ s, Polynomial.IsRoot (Polynomial.X ^ p - Polynomial.C
        ((u⁻¹ : Bˣ) * q (deltaAdjoinDivisionMap D d a (D.delta (a s)))))
        (q (deltaAdjoinDivisionVariable D d a s)) := by
  have hu : IsUnit (q (deltaAdjoinDivisionMap D d a (D.delta d))) :=
    hdist.map (q.comp (deltaAdjoinDivisionMap D d a))
  obtain ⟨u, hu⟩ := hu
  exact ⟨u, hu, fun s ↦ (deltaAdjoinDivision_variable_monic_root_residue
    D d a q hp hd u hu s).2⟩

end SerrePositivity.BhattScholze

end DeltaDivisionResidueRelation

/-! ## δ除算の二段目のモニック関係式

p,dを消す射の下でδ²(d*x)を計算する。
δ²の剰余が、δ(x)のp乗を単元係数で含むことを証明する。
有限段表示全体・除算包の平坦性の証明とは区別する。
-/

@[expose] public noncomputable section DeltaDivisionSecondResidueRelation

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {B : Type v} [CommRing B]

/-- p,dを消す通常射の下で、δ²(d*x)のδ(x)^pの係数はδ(d)^p。 -/
theorem delta_delta_mul_residue (D : DeltaStructure p A) (d x : A)
    (q : A →+* B) (hp : q (p : A) = 0) (hd : q d = 0) :
    q (D.delta (D.delta (d * x))) =
      q (D.delta (D.delta d)) * (q x) ^ (p * p) +
        q (D.delta d) ^ p * q (D.delta x) ^ p := by
  let α := d ^ p * D.delta x
  let β := D.delta d * x ^ p
  let γ := (p : A) * D.delta d * D.delta x
  have hα : q α = 0 := by simp [α, map_mul, map_pow, hd, (Fact.out : p.Prime).ne_zero]
  have hγ : q γ = 0 := by simp [γ, map_mul, hp]
  have hδα : q (D.delta α) = 0 := by
    simp only [α, D.map_delta_mul_of_prime_zero q hp, map_pow, hd,
      zero_pow (Fact.out : p.Prime).ne_zero, zero_mul,
      D.map_delta_pow_prime_of_zero q hp, zero_add]
  have hδβ : q (D.delta β) = q (D.delta (D.delta d)) * (q x) ^ (p * p) := by
    simp only [β, D.map_delta_mul_of_prime_zero q hp,
      D.map_delta_pow_prime_of_zero q hp, mul_zero, zero_add, map_pow, ← pow_mul]
  have hδγ : q (D.delta γ) = q (D.delta d) ^ p * q (D.delta x) ^ p := by
    have he : γ = (p : A) * (D.delta d * D.delta x) := mul_assoc _ _ _
    rw [he, D.map_delta_mul_of_prime_zero q hp, hp,
      zero_pow (Fact.out : p.Prime).ne_zero, zero_mul, zero_add,
      D.map_delta_prime_of_zero q hp, one_mul, map_mul, mul_pow]
  rw [D.delta_mul]
  change q (D.delta (α + β + γ)) = _
  rw [D.map_delta_add_of_right_zero q (α + β) γ hγ,
    D.map_delta_add_of_left_zero q α β hα, hδα, hδβ, hδγ, zero_add]

/-- 二段目のδ除算関係式を、δ(x)のモニック冪方程式として解く。 -/
theorem delta_mul_relation_second_residue_pow (D : DeltaStructure p A) (d x a : A)
    (h : d * x = a) (q : A →+* B) (hp : q (p : A) = 0) (hd : q d = 0)
    (u : Bˣ) (hu : (u : B) = q (D.delta d)) :
    q (D.delta x) ^ p = ((u⁻¹ : Bˣ) : B) ^ p *
      (q (D.delta (D.delta a)) - q (D.delta (D.delta d)) * (q x) ^ (p * p)) := by
  have he := congrArg (fun z ↦ q (D.delta (D.delta z))) h
  rw [delta_delta_mul_residue D d x q hp hd, ← hu] at he
  have hpow : (u : B) ^ p * q (D.delta x) ^ p =
      q (D.delta (D.delta a)) - q (D.delta (D.delta d)) * (q x) ^ (p * p) := by
    rw [← he]
    ring
  calc
    q (D.delta x) ^ p =
        (((u⁻¹ : Bˣ) : B) ^ p * (u : B) ^ p) * q (D.delta x) ^ p := by
      rw [← mul_pow]
      simp
    _ = _ := by rw [mul_assoc, hpow]

/-- 最初の冪方程式を使い、二段目の係数からxの像を除く。 -/
theorem delta_mul_relation_second_residue_pow_constant (D : DeltaStructure p A) (d x a : A)
    (h : d * x = a) (q : A →+* B) (hp : q (p : A) = 0) (hd : q d = 0)
    (u : Bˣ) (hu : (u : B) = q (D.delta d)) :
    q (D.delta x) ^ p = ((u⁻¹ : Bˣ) : B) ^ p *
      (q (D.delta (D.delta a)) - q (D.delta (D.delta d)) *
        (((u⁻¹ : Bˣ) : B) * q (D.delta a)) ^ p) := by
  have he := delta_mul_relation_second_residue_pow D d x a h q hp hd u hu
  rw [pow_mul, delta_mul_relation_residue_pow D d x a h q hp hd u hu] at he
  exact he

/-- 実際のδ添加変数のδは、(p,d)剰余で二段目の具体的な冪方程式を満たす。 -/
theorem deltaAdjoinDivision_variable_delta_pow_residue {σ : Type w}
    (D : DeltaStructure p A) (d : A) (a : σ → A)
    (q : DeltaAdjoinDivision D d a →+* B)
    (hp : q (p : DeltaAdjoinDivision D d a) = 0)
    (hd : q (deltaAdjoinDivisionMap D d a d) = 0)
    (u : Bˣ) (hu : (u : B) = q (deltaAdjoinDivisionMap D d a (D.delta d))) (s : σ) :
    q ((deltaAdjoinDivisionStructure D d a).delta (deltaAdjoinDivisionVariable D d a s)) ^ p =
      ((u⁻¹ : Bˣ) : B) ^ p *
        (q (deltaAdjoinDivisionMap D d a (D.delta (D.delta (a s)))) -
          q (deltaAdjoinDivisionMap D d a (D.delta (D.delta d))) *
            q (deltaAdjoinDivisionVariable D d a s) ^ (p * p)) := by
  let E := deltaAdjoinDivisionStructure D d a
  have hmap := deltaAdjoinDivisionMap_isDeltaHom D d a
  have hu' : (u : B) = q (E.delta (deltaAdjoinDivisionMap D d a d)) := by
    rw [← hmap d]
    exact hu
  have he := delta_mul_relation_second_residue_pow E
    (deltaAdjoinDivisionMap D d a d) (deltaAdjoinDivisionVariable D d a s)
    (deltaAdjoinDivisionMap D d a (a s)) (deltaAdjoinDivision_relation D d a s)
    q hp hd u hu'
  have h2 (z : A) : E.delta (E.delta (deltaAdjoinDivisionMap D d a z)) =
      deltaAdjoinDivisionMap D d a (D.delta (D.delta z)) := by
    rw [← hmap z, ← hmap (D.delta z)]
  rw [h2 (a s), h2 d] at he
  exact he

/-- 実際のδ添加環でも、二段目の係数を基底δデータと単元だけで表せる。 -/
theorem deltaAdjoinDivision_variable_delta_pow_residue_constant {σ : Type w}
    (D : DeltaStructure p A) (d : A) (a : σ → A)
    (q : DeltaAdjoinDivision D d a →+* B)
    (hp : q (p : DeltaAdjoinDivision D d a) = 0)
    (hd : q (deltaAdjoinDivisionMap D d a d) = 0)
    (u : Bˣ) (hu : (u : B) = q (deltaAdjoinDivisionMap D d a (D.delta d))) (s : σ) :
    q ((deltaAdjoinDivisionStructure D d a).delta (deltaAdjoinDivisionVariable D d a s)) ^ p =
      ((u⁻¹ : Bˣ) : B) ^ p *
        (q (deltaAdjoinDivisionMap D d a (D.delta (D.delta (a s)))) -
          q (deltaAdjoinDivisionMap D d a (D.delta (D.delta d))) *
            (((u⁻¹ : Bˣ) : B) * q (deltaAdjoinDivisionMap D d a (D.delta (a s)))) ^ p) := by
  have he := deltaAdjoinDivision_variable_delta_pow_residue D d a q hp hd u hu s
  rw [pow_mul, deltaAdjoinDivision_variable_pow_residue D d a q hp hd u hu s] at he
  exact he

/-- 二段目の実際の添加変数のδに対する、具体的モニック多項式と根。 -/
theorem deltaAdjoinDivision_variable_delta_monic_root_residue {σ : Type w}
    (D : DeltaStructure p A) (d : A) (a : σ → A)
    (q : DeltaAdjoinDivision D d a →+* B)
    (hp : q (p : DeltaAdjoinDivision D d a) = 0)
    (hd : q (deltaAdjoinDivisionMap D d a d) = 0)
    (u : Bˣ) (hu : (u : B) = q (deltaAdjoinDivisionMap D d a (D.delta d))) (s : σ) :
    let c := ((u⁻¹ : Bˣ) : B) ^ p *
      (q (deltaAdjoinDivisionMap D d a (D.delta (D.delta (a s)))) -
        q (deltaAdjoinDivisionMap D d a (D.delta (D.delta d))) *
          q (deltaAdjoinDivisionVariable D d a s) ^ (p * p))
    (Polynomial.X ^ p - Polynomial.C c).Monic ∧
      Polynomial.IsRoot (Polynomial.X ^ p - Polynomial.C c)
        (q ((deltaAdjoinDivisionStructure D d a).delta (deltaAdjoinDivisionVariable D d a s))) := by
  constructor
  · exact Polynomial.monic_X_pow_sub_C _ (Fact.out : p.Prime).ne_zero
  · change Polynomial.eval _ _ = 0
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      deltaAdjoinDivision_variable_delta_pow_residue D d a q hp hd u hu s, sub_self]

/-- distinguished dから二段目のモニック方程式の単元係数を供給する。 -/
theorem exists_deltaAdjoinDivision_variable_delta_monic_root_residue {σ : Type w}
    (D : DeltaStructure p A) (d : A) (a : σ → A) (hdist : D.IsDistinguished d)
    (q : DeltaAdjoinDivision D d a →+* B)
    (hp : q (p : DeltaAdjoinDivision D d a) = 0)
    (hd : q (deltaAdjoinDivisionMap D d a d) = 0) :
    ∃ u : Bˣ, (u : B) = q (deltaAdjoinDivisionMap D d a (D.delta d)) ∧
      ∀ s, Polynomial.IsRoot (Polynomial.X ^ p - Polynomial.C
        (((u⁻¹ : Bˣ) : B) ^ p *
          (q (deltaAdjoinDivisionMap D d a (D.delta (D.delta (a s)))) -
            q (deltaAdjoinDivisionMap D d a (D.delta (D.delta d))) *
              q (deltaAdjoinDivisionVariable D d a s) ^ (p * p))))
        (q ((deltaAdjoinDivisionStructure D d a).delta (deltaAdjoinDivisionVariable D d a s))) := by
  have hu : IsUnit (q (deltaAdjoinDivisionMap D d a (D.delta d))) :=
    hdist.map (q.comp (deltaAdjoinDivisionMap D d a))
  obtain ⟨u, hu⟩ := hu
  exact ⟨u, hu, fun s ↦ (deltaAdjoinDivision_variable_delta_monic_root_residue
    D d a q hp hd u hu s).2⟩

end SerrePositivity.BhattScholze

end DeltaDivisionSecondResidueRelation

/-! ## 第2有限δ関係式からのモニック冪方程式

通常射が深さ0,1,2の関係式を消すことから次の変数の冪を求める。
有限段の商のδ安定性を要求しない。
-/

@[expose] public noncomputable section DeltaDivisionSecondFiniteResidueRelation

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {B : Type v} [CommRing B]

/-- 三つの低次関係式を消す通常射の下で、δ(x)はモニック冪方程式を満たす。 -/
theorem deltaDivisionSecondRelation_pow_of_vanishing
    (D : DeltaStructure p A) (q : A →+* B) (d x a : A)
    (hp : q (p : A) = 0) (hd : q d = 0)
    (h0 : q (d * x - a) = 0) (h1 : q (D.delta (d * x - a)) = 0)
    (h2 : q (D.delta (D.delta (d * x - a))) = 0)
    (u : Bˣ) (hu : (u : B) = q (D.delta d)) :
    q (D.delta x) ^ p = ((u⁻¹ : Bˣ) : B) ^ p *
      (q (D.delta (D.delta a)) - q (D.delta (D.delta d)) * (q x) ^ (p * p)) := by
  have ha : q a = 0 := by
    simpa only [map_sub, map_mul, hd, zero_mul, zero_sub, neg_eq_zero] using h0
  have he := D.map_delta_delta_eq_of_difference_zero q hp (d * x) a ha h0 h1 h2
  rw [delta_delta_mul_residue D d x q hp hd, ← hu] at he
  have hpow : (u : B) ^ p * q (D.delta x) ^ p =
      q (D.delta (D.delta a)) - q (D.delta (D.delta d)) * (q x) ^ (p * p) := by
    rw [← he]
    ring
  calc
    q (D.delta x) ^ p =
        (((u⁻¹ : Bˣ) : B) ^ p * (u : B) ^ p) * q (D.delta x) ^ p := by
      rw [← mul_pow]
      simp
    _ = _ := by rw [mul_assoc, hpow]

/-- 三つの低次関係式の消滅から、次の根の係数を基底データだけで表す。 -/
theorem deltaDivisionSecondRelation_pow_constant_of_vanishing
    (D : DeltaStructure p A) (q : A →+* B) (d x a : A)
    (hp : q (p : A) = 0) (hd : q d = 0)
    (h0 : q (d * x - a) = 0) (h1 : q (D.delta (d * x - a)) = 0)
    (h2 : q (D.delta (D.delta (d * x - a))) = 0)
    (u : Bˣ) (hu : (u : B) = q (D.delta d)) :
    q (D.delta x) ^ p = ((u⁻¹ : Bˣ) : B) ^ p *
      (q (D.delta (D.delta a)) - q (D.delta (D.delta d)) *
        (((u⁻¹ : Bˣ) : B) * q (D.delta a)) ^ p) := by
  have he := deltaDivisionSecondRelation_pow_of_vanishing D q d x a hp hd h0 h1 h2 u hu
  rw [pow_mul, deltaDivisionFirstRelation_pow_of_vanishing D q d x a hp hd h0 h1 u hu] at he
  exact he

/-- 相対自由δ環の深さ0,1,2の関係式から、第1δ変数の具体的な冪を得る。 -/
theorem deltaDivisionFiniteSecondRoot_pow {σ : Type w}
    (D : DeltaStructure p A) (d : A) (a : σ → A)
    (q : RelativeFreeDeltaRing (R := A) σ →+* B)
    (hp : q (p : RelativeFreeDeltaRing (R := A) σ) = 0)
    (hd : q (MvPolynomial.C d) = 0)
    (hrel : ∀ s n, n ≤ 2 → q (deltaDivisionIteratedRelation D d a s n) = 0)
    (u : Bˣ) (hu : (u : B) = q (MvPolynomial.C (D.delta d))) (s : σ) :
    q (MvPolynomial.X (s, 1)) ^ p = ((u⁻¹ : Bˣ) : B) ^ p *
      (q (MvPolynomial.C (D.delta (D.delta (a s)))) -
        q (MvPolynomial.C (D.delta (D.delta d))) *
          (((u⁻¹ : Bˣ) : B) * q (MvPolynomial.C (D.delta (a s)))) ^ p) := by
  have h := deltaDivisionSecondRelation_pow_constant_of_vanishing
    (relativeFreeDeltaStructure σ D) q (MvPolynomial.C d) (MvPolynomial.X (s, 0))
    (MvPolynomial.C (a s)) hp hd (hrel s 0 (by decide)) (hrel s 1 (by decide))
    (hrel s 2 le_rfl) u (by simpa only [relativeFreeDeltaStructure_delta_C] using hu)
  simpa only [relativeFreeDeltaStructure_delta_C, relativeFreeDeltaStructure_delta_X] using h

end SerrePositivity.BhattScholze

end DeltaDivisionSecondFiniteResidueRelation

/-! ## 第2有限段の関係式消滅の逆向き比較と実際の商

有限深さの商のδ安定性を要求せず、二つのモニック方程式を比較する。
-/

@[expose] public noncomputable section DeltaDivisionSecondFinitePresentation

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {B : Type v} [CommRing B]

/-- 最初の二つの関係式が消える場合、第2δ関係式と次の冪方程式は同値。 -/
theorem deltaDivisionSecondRelation_vanish_iff_pow
    (D : DeltaStructure p A) (q : A →+* B) (d x a : A)
    (hp : q (p : A) = 0) (hd : q d = 0)
    (h0 : q (d * x - a) = 0) (h1 : q (D.delta (d * x - a)) = 0)
    (u : Bˣ) (hu : (u : B) = q (D.delta d)) :
    q (D.delta (D.delta (d * x - a))) = 0 ↔
      q (D.delta x) ^ p = ((u⁻¹ : Bˣ) : B) ^ p *
        (q (D.delta (D.delta a)) - q (D.delta (D.delta d)) * (q x) ^ (p * p)) := by
  constructor
  · intro h2
    exact deltaDivisionSecondRelation_pow_of_vanishing D q d x a hp hd h0 h1 h2 u hu
  · intro hpow
    have ha : q a = 0 := by
      simpa only [map_sub, map_mul, hd, zero_mul, zero_sub, neg_eq_zero] using h0
    have he := D.map_delta_delta_add_of_zero q hp (d * x - a) a h0 ha h1
    rw [sub_add_cancel] at he
    have hinv : (u : B) ^ p * ((u⁻¹ : Bˣ) : B) ^ p = 1 := by
      rw [← mul_pow]
      simp
    have hda : q (D.delta (D.delta (d * x))) = q (D.delta (D.delta a)) := by
      rw [delta_delta_mul_residue D d x q hp hd, ← hu, hpow, ← mul_assoc, hinv, one_mul]
      ring
    rw [he] at hda
    exact add_right_cancel (hda.trans (zero_add _).symm)

/-- 三つの低次関係式の消滅は、係数の消滅と二つのモニック方程式に同値。 -/
theorem deltaDivisionThreeRelations_vanish_iff
    (D : DeltaStructure p A) (q : A →+* B) (d x a : A)
    (hp : q (p : A) = 0) (hd : q d = 0)
    (u : Bˣ) (hu : (u : B) = q (D.delta d)) :
    (q (d * x - a) = 0 ∧ q (D.delta (d * x - a)) = 0 ∧
      q (D.delta (D.delta (d * x - a))) = 0) ↔
    (q a = 0 ∧ (q x) ^ p = (u⁻¹ : Bˣ) * q (D.delta a) ∧
      q (D.delta x) ^ p = ((u⁻¹ : Bˣ) : B) ^ p *
        (q (D.delta (D.delta a)) - q (D.delta (D.delta d)) *
          (((u⁻¹ : Bˣ) : B) * q (D.delta a)) ^ p)) := by
  constructor
  · rintro ⟨h0, h1, h2⟩
    have he := (deltaDivisionFirstRelations_vanish_iff D q d x a hp hd u hu).mp ⟨h0, h1⟩
    exact ⟨he.1, he.2,
      deltaDivisionSecondRelation_pow_constant_of_vanishing D q d x a hp hd h0 h1 h2 u hu⟩
  · rintro ⟨ha, hpow0, hpow1⟩
    have he := (deltaDivisionFirstRelations_vanish_iff D q d x a hp hd u hu).mpr ⟨ha, hpow0⟩
    refine ⟨he.1, he.2, ?_⟩
    apply (deltaDivisionSecondRelation_vanish_iff_pow D q d x a hp hd he.1 he.2 u hu).mpr
    simpa only [pow_mul, hpow0] using hpow1

variable {σ : Type w}

/-- 有限深さの関係式イデアルは次の段の関係式を添加して得られる。
任意Nに対する通常イデアルの等式であり、δ安定性は要求しない。 -/
theorem deltaDivisionFiniteRelationIdeal_succ
    (D : DeltaStructure p A) (d : A) (a : σ → A) (N : ℕ) :
    deltaDivisionFiniteRelationIdeal D d a (N + 1) =
      deltaDivisionFiniteRelationIdeal D d a N ⊔
        Ideal.span (Set.range fun s => deltaDivisionIteratedRelation D d a s (N + 1)) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨s, n⟩, rfl⟩
    change deltaDivisionIteratedRelation D d a s n.val ∈ _
    by_cases hn : n.val < N + 1
    · apply (show deltaDivisionFiniteRelationIdeal D d a N ≤
        deltaDivisionFiniteRelationIdeal D d a N ⊔ _ from le_sup_left)
      exact Ideal.subset_span (Set.mem_range.mpr ⟨(s, ⟨n.val, hn⟩), rfl⟩)
    · have he : n.val = N + 1 := by omega
      rw [he]
      apply (show Ideal.span (Set.range fun t => deltaDivisionIteratedRelation D d a t (N + 1)) ≤
        deltaDivisionFiniteRelationIdeal D d a N ⊔ _ from le_sup_right)
      exact Ideal.subset_span (Set.mem_range_self s)
  · apply sup_le
    · exact deltaDivisionFiniteRelationIdeal_mono D d a (Nat.le_succ N)
    · apply Ideal.span_le.mpr
      rintro _ ⟨s, rfl⟩
      exact Ideal.subset_span (Set.mem_range.mpr ⟨(s, ⟨N + 1, Nat.lt_succ_self _⟩), rfl⟩)

/-- p,dと深さ2以下のδ関係式を課した実際の通常イデアル。 -/
def deltaDivisionSecondResidueIdeal (D : DeltaStructure p A) (d : A) (a : σ → A) :
    Ideal (RelativeFreeDeltaRing (R := A) σ) :=
  Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ⊔
    deltaDivisionFiniteRelationIdeal D d a 2

/-- 実際の第2通常商で、次の変数は基底データで指定したp乗根となる。 -/
theorem deltaDivisionSecondResidueQuotient_root_pow
    (D : DeltaStructure p A) (d : A) (a : σ → A)
    (u : Aˣ) (hu : (u : A) = D.delta d) (s : σ) :
    let q := Ideal.Quotient.mk (deltaDivisionSecondResidueIdeal D d a)
    q (MvPolynomial.X (s, 1)) ^ p = q (MvPolynomial.C
      (((u⁻¹ : Aˣ) : A) ^ p * (D.delta (D.delta (a s)) - D.delta (D.delta d) *
        (((u⁻¹ : Aˣ) : A) * D.delta (a s)) ^ p))) := by
  let J := deltaDivisionSecondResidueIdeal D d a
  let q := Ideal.Quotient.mk J
  let f := q.comp (MvPolynomial.C : A →+* RelativeFreeDeltaRing (R := A) σ)
  have hbase : Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ≤ J :=
    le_sup_left
  have hp : q (p : RelativeFreeDeltaRing (R := A) σ) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hbase (Ideal.subset_span (by simp)))
  have hd : q (MvPolynomial.C d) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hbase (Ideal.subset_span (by simp)))
  have hrel : ∀ t n, n ≤ 2 → q (deltaDivisionIteratedRelation D d a t n) = 0 := by
    intro t n hn
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply (show deltaDivisionFiniteRelationIdeal D d a 2 ≤ J from le_sup_right)
    exact Ideal.subset_span (Set.mem_range.mpr ⟨(t, ⟨n, Nat.lt_succ_of_le hn⟩), rfl⟩)
  have hunit : ((u.map f : (RelativeFreeDeltaRing (R := A) σ ⧸ J)ˣ) :
      RelativeFreeDeltaRing (R := A) σ ⧸ J) = q (MvPolynomial.C (D.delta d)) := by
    change f (u : A) = _
    rw [hu]
    rfl
  have he := deltaDivisionFiniteSecondRoot_pow D d a q hp hd hrel (u.map f) hunit s
  change _ = f _
  rw [map_mul, map_pow, map_sub, map_mul, map_pow, map_mul]
  exact he

/-- 実際の第2剰余イデアルは初期剰余イデアルに第2関係式を加えたもの。 -/
theorem deltaDivisionSecondResidueIdeal_eq_first_sup
    (D : DeltaStructure p A) (d : A) (a : σ → A) :
    deltaDivisionSecondResidueIdeal D d a = deltaDivisionFirstResidueIdeal D d a ⊔
      Ideal.span (Set.range fun s => deltaDivisionIteratedRelation D d a s 2) := by
  change Ideal.span _ ⊔ deltaDivisionFiniteRelationIdeal D d a (1 + 1) = _
  rw [deltaDivisionFiniteRelationIdeal_succ, ← sup_assoc]
  rfl

end SerrePositivity.BhattScholze

end DeltaDivisionSecondFinitePresentation

/-! ## 最初のδ除算剰余のモニック関係式表示

深さ0,1の通常イデアルを、係数関係式と初期変数のモニック冪関係式へ同定する。
全δ段・完備化・perfectionの平坦性は別工程。
-/

@[expose] public noncomputable section DeltaDivisionFirstResiduePresentation

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 係数と初期モニック冪関係式で生成する通常イデアル。 -/
def deltaDivisionFirstMonicIdeal (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :
    Ideal (RelativeFreeDeltaRing (R := A) σ) :=
  (Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ⊔
    Ideal.span (Set.range fun s => MvPolynomial.C (a s))) ⊔
    Ideal.span (Set.range fun s => MvPolynomial.X (s, 0) ^ p -
      MvPolynomial.C ((u⁻¹ : Aˣ) * D.delta (a s)))

/-- 深さ0,1の通常イデアルを消すための具体的な判定。 -/
theorem deltaDivisionFirstResidueIdeal_le_ker_iff
    {B : Type w} [CommRing B] (D : DeltaStructure p A) (d : A) (a : σ → A)
    (q : RelativeFreeDeltaRing (R := A) σ →+* B) :
    deltaDivisionFirstResidueIdeal D d a ≤ RingHom.ker q ↔
      q (p : RelativeFreeDeltaRing (R := A) σ) = 0 ∧ q (MvPolynomial.C d) = 0 ∧
        ∀ s, q (deltaDivisionIteratedRelation D d a s 0) = 0 ∧
          q (deltaDivisionIteratedRelation D d a s 1) = 0 := by
  constructor
  · intro h
    have hbase : Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ≤
        deltaDivisionFirstResidueIdeal D d a := le_sup_left
    have hrel : deltaDivisionFiniteRelationIdeal D d a 1 ≤
        deltaDivisionFirstResidueIdeal D d a := le_sup_right
    refine ⟨h (hbase (Ideal.subset_span (by simp))),
      h (hbase (Ideal.subset_span (by simp))), fun s => ⟨?_, ?_⟩⟩
    · exact h (hrel (Ideal.subset_span (Set.mem_range.mpr ⟨(s, ⟨0, by decide⟩), rfl⟩)))
    · exact h (hrel (Ideal.subset_span (Set.mem_range.mpr ⟨(s, ⟨1, by decide⟩), rfl⟩)))
  · rintro ⟨hp, hd, hrel⟩
    apply sup_le
    · apply Ideal.span_le.mpr
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact hp
      · exact hd
    · apply Ideal.span_le.mpr
      rintro _ ⟨⟨s, n⟩, rfl⟩
      change q (deltaDivisionIteratedRelation D d a s n.val) = 0
      have hn : n.val = 0 ∨ n.val = 1 := by omega
      rcases hn with hn | hn
      · simpa only [hn] using (hrel s).1
      · simpa only [hn] using (hrel s).2

/-- モニック表示の通常イデアルを消すための具体的な判定。 -/
theorem deltaDivisionFirstMonicIdeal_le_ker_iff
    {B : Type w} [CommRing B] (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ)
    (q : RelativeFreeDeltaRing (R := A) σ →+* B) :
    deltaDivisionFirstMonicIdeal D d a u ≤ RingHom.ker q ↔
      q (p : RelativeFreeDeltaRing (R := A) σ) = 0 ∧ q (MvPolynomial.C d) = 0 ∧
        ∀ s, q (MvPolynomial.C (a s)) = 0 ∧
          (q (MvPolynomial.X (s, 0))) ^ p =
            q (MvPolynomial.C ((u⁻¹ : Aˣ) * D.delta (a s))) := by
  constructor
  · intro h
    have hb : Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ≤
        deltaDivisionFirstMonicIdeal D d a u := le_sup_left.trans le_sup_left
    have ha : Ideal.span (Set.range fun s => MvPolynomial.C (a s)) ≤
        deltaDivisionFirstMonicIdeal D d a u := le_sup_right.trans le_sup_left
    have hm : Ideal.span (Set.range fun s => MvPolynomial.X (s, 0) ^ p -
        MvPolynomial.C ((u⁻¹ : Aˣ) * D.delta (a s))) ≤
        deltaDivisionFirstMonicIdeal D d a u := le_sup_right
    refine ⟨h (hb (Ideal.subset_span (by simp))), h (hb (Ideal.subset_span (by simp))),
      fun s => ⟨h (ha (Ideal.subset_span (Set.mem_range_self s))), ?_⟩⟩
    have he := h (hm (Ideal.subset_span (Set.mem_range_self s)))
    change q (_ - _) = 0 at he
    simpa only [map_sub, map_pow, sub_eq_zero] using he
  · rintro ⟨hp, hd, hs⟩
    apply sup_le
    · apply sup_le
      · apply Ideal.span_le.mpr
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact hp
        · exact hd
      · apply Ideal.span_le.mpr
        rintro _ ⟨s, rfl⟩
        exact (hs s).1
    · apply Ideal.span_le.mpr
      rintro _ ⟨s, rfl⟩
      change q (_ - _) = 0
      rw [map_sub, map_pow, (hs s).2, sub_self]

/-- 元の低次イデアルとモニック表示イデアルは同じ通常射を消す。 -/
theorem deltaDivisionFirstResidue_monic_le_ker_iff
    {B : Type w} [CommRing B] (D : DeltaStructure p A) (d : A) (a : σ → A)
    (u : Aˣ) (hu : (u : A) = D.delta d)
    (q : RelativeFreeDeltaRing (R := A) σ →+* B) :
    deltaDivisionFirstResidueIdeal D d a ≤ RingHom.ker q ↔
      deltaDivisionFirstMonicIdeal D d a u ≤ RingHom.ker q := by
  rw [deltaDivisionFirstResidueIdeal_le_ker_iff, deltaDivisionFirstMonicIdeal_le_ker_iff]
  let f := q.comp (MvPolynomial.C : A →+* RelativeFreeDeltaRing (R := A) σ)
  have hunit : ((u.map f : Bˣ) : B) =
      q ((relativeFreeDeltaStructure σ D).delta (MvPolynomial.C d)) := by
    change f (u : A) = _
    rw [hu, relativeFreeDeltaStructure_delta_C]
    rfl
  have hcoeff (s : σ) : (u.map f)⁻¹.val *
      q ((relativeFreeDeltaStructure σ D).delta (MvPolynomial.C (a s))) =
      q (MvPolynomial.C ((u⁻¹ : Aˣ) * D.delta (a s))) := by
    rw [relativeFreeDeltaStructure_delta_C, map_mul, map_mul]
    rfl
  constructor
  · rintro ⟨hp, hd, hs⟩
    refine ⟨hp, hd, fun s => ?_⟩
    have he := (deltaDivisionFirstRelations_vanish_iff (relativeFreeDeltaStructure σ D) q
      (MvPolynomial.C d) (MvPolynomial.X (s, 0)) (MvPolynomial.C (a s)) hp hd
      (u.map f) hunit).mp (hs s)
    simpa only [hcoeff] using he
  · rintro ⟨hp, hd, hs⟩
    refine ⟨hp, hd, fun s => ?_⟩
    apply (deltaDivisionFirstRelations_vanish_iff (relativeFreeDeltaStructure σ D) q
      (MvPolynomial.C d) (MvPolynomial.X (s, 0)) (MvPolynomial.C (a s)) hp hd
      (u.map f) hunit).mpr
    simpa only [hcoeff] using hs s

/-- 実際の低次通常イデアルは、係数関係式とモニック冪関係式のイデアル。 -/
theorem deltaDivisionFirstResidueIdeal_eq_monic
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) :
    deltaDivisionFirstResidueIdeal D d a = deltaDivisionFirstMonicIdeal D d a u := by
  apply le_antisymm
  · have h : deltaDivisionFirstMonicIdeal D d a u ≤
        RingHom.ker (Ideal.Quotient.mk (deltaDivisionFirstMonicIdeal D d a u)) :=
      fun x hx => Ideal.Quotient.eq_zero_iff_mem.mpr hx
    have he := (deltaDivisionFirstResidue_monic_le_ker_iff D d a u hu _).mpr h
    exact fun x hx => Ideal.Quotient.eq_zero_iff_mem.mp (he hx)
  · have h : deltaDivisionFirstResidueIdeal D d a ≤
        RingHom.ker (Ideal.Quotient.mk (deltaDivisionFirstResidueIdeal D d a)) :=
      fun x hx => Ideal.Quotient.eq_zero_iff_mem.mpr hx
    have he := (deltaDivisionFirstResidue_monic_le_ker_iff D d a u hu _).mp h
    exact fun x hx => Ideal.Quotient.eq_zero_iff_mem.mp (he hx)

/-- 実際の低次商とモニック関係式商の標準同型。 -/
def deltaDivisionFirstResidueMonicEquiv
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) :
    (RelativeFreeDeltaRing (R := A) σ ⧸ deltaDivisionFirstResidueIdeal D d a) ≃+*
      (RelativeFreeDeltaRing (R := A) σ ⧸ deltaDivisionFirstMonicIdeal D d a u) :=
  Ideal.quotEquivOfEq (deltaDivisionFirstResidueIdeal_eq_monic D d a u hu)

/-- 低次モニック商同型は標準商射と両立する。 -/
@[simp] theorem deltaDivisionFirstResidueMonicEquiv_mk
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d)
    (x : RelativeFreeDeltaRing (R := A) σ) :
    deltaDivisionFirstResidueMonicEquiv D d a u hu
      (Ideal.Quotient.mk (deltaDivisionFirstResidueIdeal D d a) x) =
        Ideal.Quotient.mk (deltaDivisionFirstMonicIdeal D d a u) x :=
  Ideal.quotEquivOfEq_mk _ x

end SerrePositivity.BhattScholze

end DeltaDivisionFirstResiduePresentation

/-! ## 初期δ剰余を係数とする後続変数の多項式表示

初期モニック関係式を係数イデアルへ移し、既存多項式商同型を使う。
この係数商の根添加環表示と、全δ段の平坦性は別途比較する。
-/

@[expose] public noncomputable section DeltaDivisionFirstResiduePowerPresentation

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 初期変数のみの多項式環に置いた係数・モニック関係式のイデアル。 -/
def deltaDivisionFirstPolynomialIdeal (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :
    Ideal (MvPolynomial σ A) :=
  (Ideal.span {(p : MvPolynomial σ A), MvPolynomial.C d} ⊔
    Ideal.span (Set.range fun s => MvPolynomial.C (a s))) ⊔
    Ideal.span (Set.range fun s => MvPolynomial.X s ^ p -
      MvPolynomial.C ((u⁻¹ : Aˣ) * D.delta (a s)))

/-- 変数分離は初期モニックイデアルを係数イデアルの延長へ送る。 -/
theorem deltaDivisionFirstMonicIdeal_map_split
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :
    (deltaDivisionFirstMonicIdeal D d a u).map
      (relativeFreeVariableSplitAlgEquiv σ A).toRingHom =
      (deltaDivisionFirstPolynomialIdeal D d a u).map
        (MvPolynomial.C : MvPolynomial σ A →+* MvPolynomial (σ × ℕ) (MvPolynomial σ A)) := by
  simp only [deltaDivisionFirstMonicIdeal, deltaDivisionFirstPolynomialIdeal,
    Ideal.map_sup, Ideal.map_span, Set.image_pair, ← Set.range_comp']
  simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    AlgEquiv.coe_toRingEquiv, map_natCast, relativeFreeVariableSplitAlgEquiv_C,
    relativeFreeVariableSplitAlgEquiv_X_zero, map_sub, map_pow]

/-- 実際の低次δ剰余イデアルも、係数イデアルの延長へ送られる。 -/
theorem deltaDivisionFirstResidueIdeal_map_split
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) :
    (deltaDivisionFirstResidueIdeal D d a).map
      (relativeFreeVariableSplitAlgEquiv σ A).toRingHom =
      (deltaDivisionFirstPolynomialIdeal D d a u).map
        (MvPolynomial.C : MvPolynomial σ A →+* MvPolynomial (σ × ℕ) (MvPolynomial σ A)) := by
  rw [deltaDivisionFirstResidueIdeal_eq_monic D d a u hu,
    deltaDivisionFirstMonicIdeal_map_split]

/-- 実際の初期δ剰余は、初期関係式の商上の後続変数の多項式環。 -/
def deltaDivisionFirstResiduePolynomialEquiv
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) :
    (RelativeFreeDeltaRing (R := A) σ ⧸ deltaDivisionFirstResidueIdeal D d a) ≃+*
      MvPolynomial (σ × ℕ) (MvPolynomial σ A ⧸ deltaDivisionFirstPolynomialIdeal D d a u) :=
  (Ideal.quotientEquiv _ _ (relativeFreeVariableSplitAlgEquiv σ A).toRingEquiv
    (deltaDivisionFirstResidueIdeal_map_split D d a u hu).symm).trans
    (MvPolynomial.quotientEquivQuotientMvPolynomial
      (σ := σ × ℕ) (deltaDivisionFirstPolynomialIdeal D d a u)).symm.toRingEquiv

/-- 後続多項式表示は標準商射と係数の標準商写像に両立する。 -/
theorem deltaDivisionFirstResiduePolynomialEquiv_mk
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d)
    (x : RelativeFreeDeltaRing (R := A) σ) :
    deltaDivisionFirstResiduePolynomialEquiv D d a u hu
      (Ideal.Quotient.mk (deltaDivisionFirstResidueIdeal D d a) x) =
      MvPolynomial.map (Ideal.Quotient.mk (deltaDivisionFirstPolynomialIdeal D d a u))
        (relativeFreeVariableSplitAlgEquiv σ A x) := by
  change MvPolynomial.eval₂Hom
    (MvPolynomial.C.comp (Ideal.Quotient.mk (deltaDivisionFirstPolynomialIdeal D d a u)))
    MvPolynomial.X (relativeFreeVariableSplitAlgEquiv σ A x) = _
  rw [MvPolynomial.map_eq_eval₂Hom_C_comp]

/-- 初期変数の剰余は係数商の指定変数となる。 -/
@[simp] theorem deltaDivisionFirstResiduePolynomialEquiv_initial
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d)
    (s : σ) :
    deltaDivisionFirstResiduePolynomialEquiv D d a u hu
      (Ideal.Quotient.mk (deltaDivisionFirstResidueIdeal D d a) (MvPolynomial.X (s, 0))) =
      MvPolynomial.C (Ideal.Quotient.mk (deltaDivisionFirstPolynomialIdeal D d a u)
        (MvPolynomial.X s)) := by
  rw [deltaDivisionFirstResiduePolynomialEquiv_mk,
    relativeFreeVariableSplitAlgEquiv_X_zero, MvPolynomial.map_C]

/-- 後続δ変数の剰余は外側の自由変数となる。 -/
@[simp] theorem deltaDivisionFirstResiduePolynomialEquiv_successor
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d)
    (s : σ) (n : ℕ) :
    deltaDivisionFirstResiduePolynomialEquiv D d a u hu
      (Ideal.Quotient.mk (deltaDivisionFirstResidueIdeal D d a) (MvPolynomial.X (s, n + 1))) =
      MvPolynomial.X (s, n) := by
  rw [deltaDivisionFirstResiduePolynomialEquiv_mk,
    relativeFreeVariableSplitAlgEquiv_X_succ, MvPolynomial.map_X]

/-- 元の係数の剰余は係数商の標準像となる。 -/
@[simp] theorem deltaDivisionFirstResiduePolynomialEquiv_coeff
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d)
    (r : A) :
    deltaDivisionFirstResiduePolynomialEquiv D d a u hu
      (Ideal.Quotient.mk (deltaDivisionFirstResidueIdeal D d a) (MvPolynomial.C r)) =
      MvPolynomial.C (Ideal.Quotient.mk (deltaDivisionFirstPolynomialIdeal D d a u)
        (MvPolynomial.C r)) := by
  rw [deltaDivisionFirstResiduePolynomialEquiv_mk,
    relativeFreeVariableSplitAlgEquiv_C, MvPolynomial.map_C]

end SerrePositivity.BhattScholze

end DeltaDivisionFirstResiduePowerPresentation

/-! ## 第一δ除算関係式の二次誤差を含む具体的正規形

減算補正をイデアルの二乗で追い、次のδ計算へ渡せる代表元を示す。
-/

@[expose] public noncomputable section DeltaDivisionFirstOrderNormalForm

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 基底係数倍の有限δ像を、基底Frobeniusとδの係数で正確に表す。 -/
theorem relativeFreeFiniteDeltaStep_coefficient_mul (N : ℕ) (D : DeltaStructure p A)
    (d : A) (f : MvPolynomial (σ × Fin (N + 1)) A) :
    relativeFreeFiniteDeltaStep N σ D (MvPolynomial.C d * f) =
      MvPolynomial.C (D.frobeniusLift d) * relativeFreeFiniteDeltaStep N σ D f +
        MvPolynomial.C (D.delta d) * (relativeFreeFiniteStepInclusion N σ f) ^ p := by
  have hC : relativeFreeFiniteStepInclusion N σ (MvPolynomial.C d) = MvPolynomial.C d := by
    change MvPolynomial.rename _ (MvPolynomial.C d) = _
    exact MvPolynomial.rename_C _ d
  rw [relativeFreeFiniteDeltaStep_mul, hC, relativeFreeFiniteDeltaStep_C,
    D.frobeniusLift_apply, map_add, map_mul, map_pow, map_natCast]
  ring

/-- 通常除算関係式の有限δ像の正規形からの差は、二入力を含むイデアルの二乗。 -/
theorem relativeFreeFiniteDeltaStep_division_normalForm_mem_square (N : ℕ)
    (D : DeltaStructure p A) (d a : A) (f : MvPolynomial (σ × Fin (N + 1)) A)
    (I : Ideal (MvPolynomial (σ × Fin (N + 2)) A))
    (hd : MvPolynomial.C d ∈ I) (ha : MvPolynomial.C a ∈ I) :
    relativeFreeFiniteDeltaStep N σ D (MvPolynomial.C d * f - MvPolynomial.C a) -
      (MvPolynomial.C (D.frobeniusLift d) * relativeFreeFiniteDeltaStep N σ D f +
        MvPolynomial.C (D.delta d) * (relativeFreeFiniteStepInclusion N σ f) ^ p -
          MvPolynomial.C (D.delta a)) ∈ I ^ 2 := by
  have hC (z : A) : relativeFreeFiniteStepInclusion N σ (MvPolynomial.C z) = MvPolynomial.C z := by
    change MvPolynomial.rename _ (MvPolynomial.C z) = _
    exact MvPolynomial.rename_C _ z
  have hdf : relativeFreeFiniteStepInclusion N σ (MvPolynomial.C d * f) ∈ I := by
    rw [map_mul, hC]
    exact I.mul_mem_right _ hd
  have he := relativeFreeFiniteDeltaStep_sub_error_mem_square N σ D I
    (MvPolynomial.C d * f) (MvPolynomial.C a) hdf (by simpa only [hC] using ha)
  rw [relativeFreeFiniteDeltaStep_coefficient_mul, relativeFreeFiniteDeltaStep_C] at he
  exact he

/-- 第一反復関係式を具体的な二次誤差付き正規形にする、全段帰納の初期段。 -/
theorem deltaDivisionFiniteRelationPolynomial_one_normalForm_mem_square
    (D : DeltaStructure p A) (d : A) (a : σ → A) (s : σ)
    (I : Ideal (MvPolynomial (σ × Fin 2) A))
    (hd : MvPolynomial.C d ∈ I) (ha : MvPolynomial.C (a s) ∈ I) :
    deltaDivisionFiniteRelationPolynomial D d a s 1 -
      (MvPolynomial.C (D.frobeniusLift d) * MvPolynomial.X (s, 1) +
        MvPolynomial.C (D.delta d) * MvPolynomial.X (s, 0) ^ p -
          MvPolynomial.C (D.delta (a s))) ∈ I ^ 2 := by
  have he := relativeFreeFiniteDeltaStep_division_normalForm_mem_square 0 D d (a s)
    (MvPolynomial.X (s, 0)) I hd ha
  simpa [deltaDivisionFiniteRelationPolynomial, relativeFreeFiniteDeltaStep_X,
    relativeFreeFiniteStepInclusion] using he

/-- 第二反復関係式の通常p剰余像は、第一段の具体的正規形にδを適用して計算できる。 -/
theorem deltaDivisionFiniteRelationPolynomial_two_image_of_normalForm
    {B : Type w} [CommRing B] (D : DeltaStructure p A) (d : A) (a : σ → A) (s : σ)
    (q : MvPolynomial (σ × Fin 3) A →+* B)
    (hp : q (p : MvPolynomial (σ × Fin 3) A) = 0)
    (hd : q (MvPolynomial.C d) = 0) (ha : q (MvPolynomial.C (a s)) = 0) :
    q (deltaDivisionFiniteRelationPolynomial D d a s 2) =
      q (relativeFreeFiniteDeltaStep 1 σ D
        (MvPolynomial.C (D.frobeniusLift d) * MvPolynomial.X (s, 1) +
          MvPolynomial.C (D.delta d) * MvPolynomial.X (s, 0) ^ p -
            MvPolynomial.C (D.delta (a s)))) := by
  rw [deltaDivisionFiniteRelationPolynomial_succ]
  apply relativeFreeFiniteDeltaStep_map_eq_of_sub_mem_ker_square 1 σ D q hp
  apply deltaDivisionFiniteRelationPolynomial_one_normalForm_mem_square
  · change q (relativeFreeFiniteStepInclusion 1 σ (MvPolynomial.C d)) = 0
    simpa [relativeFreeFiniteStepInclusion] using hd
  · change q (relativeFreeFiniteStepInclusion 1 σ (MvPolynomial.C (a s))) = 0
    simpa [relativeFreeFiniteStepInclusion] using ha

end SerrePositivity.BhattScholze

end DeltaDivisionFirstOrderNormalForm

/-! ## 第2通常δ剰余のモニック関係式イデアル

実際の第2剰余イデアルを二つのモニック冪方程式のイデアルへ同定する。
-/

@[expose] public noncomputable section DeltaDivisionSecondMonicPresentation

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 次のδ変数のモニック冪方程式の係数。基底δデータだけで表す。 -/
def deltaDivisionSecondPowerCoefficient (D : DeltaStructure p A) (a : σ → A) (d : A)
    (u : Aˣ) (s : σ) : A :=
  ((u⁻¹ : Aˣ) : A) ^ p * (D.delta (D.delta (a s)) - D.delta (D.delta d) *
    (((u⁻¹ : Aˣ) : A) * D.delta (a s)) ^ p)

/-- 初期モニックイデアルに次のモニック方程式を加えた通常イデアル。 -/
def deltaDivisionSecondMonicIdeal (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :
    Ideal (RelativeFreeDeltaRing (R := A) σ) :=
  deltaDivisionFirstMonicIdeal D d a u ⊔ Ideal.span (Set.range fun s =>
    MvPolynomial.X (s, 1) ^ p - MvPolynomial.C (deltaDivisionSecondPowerCoefficient D a d u s))

/-- 初期関係式を消す通常射について、第2関係式と次の冪方程式は同値。 -/
theorem deltaDivisionSecondIteratedRelation_vanish_iff_root
    {B : Type w} [CommRing B] (D : DeltaStructure p A) (d : A) (a : σ → A)
    (u : Aˣ) (hu : (u : A) = D.delta d)
    (q : RelativeFreeDeltaRing (R := A) σ →+* B)
    (hp : q (p : RelativeFreeDeltaRing (R := A) σ) = 0) (hd : q (MvPolynomial.C d) = 0)
    (s : σ) (h0 : q (deltaDivisionIteratedRelation D d a s 0) = 0)
    (h1 : q (deltaDivisionIteratedRelation D d a s 1) = 0) :
    q (deltaDivisionIteratedRelation D d a s 2) = 0 ↔
      q (MvPolynomial.X (s, 1)) ^ p =
        q (MvPolynomial.C (deltaDivisionSecondPowerCoefficient D a d u s)) := by
  let F := relativeFreeDeltaStructure σ D
  let f := q.comp (MvPolynomial.C : A →+* RelativeFreeDeltaRing (R := A) σ)
  have hunit : ((u.map f : Bˣ) : B) = q (F.delta (MvPolynomial.C d)) := by
    change f (u : A) = _
    rw [hu, relativeFreeDeltaStructure_delta_C]
    rfl
  have hpow := deltaDivisionFirstRelation_pow_of_vanishing F q (MvPolynomial.C d)
    (MvPolynomial.X (s, 0)) (MvPolynomial.C (a s)) hp hd h0 h1 (u.map f) hunit
  have he := deltaDivisionSecondRelation_vanish_iff_pow F q (MvPolynomial.C d)
    (MvPolynomial.X (s, 0)) (MvPolynomial.C (a s)) hp hd h0 h1 (u.map f) hunit
  rw [pow_mul, hpow] at he
  have hcoeff : ((u.map f)⁻¹ : Bˣ) ^ p *
      (q (F.delta (F.delta (MvPolynomial.C (a s)))) -
        q (F.delta (F.delta (MvPolynomial.C d))) *
          (((u.map f)⁻¹ : Bˣ) * q (F.delta (MvPolynomial.C (a s)))) ^ p) =
      q (MvPolynomial.C (deltaDivisionSecondPowerCoefficient D a d u s)) := by
    simp only [F, relativeFreeDeltaStructure_delta_C, deltaDivisionSecondPowerCoefficient,
      map_mul, map_pow, map_sub]
    rfl
  rw [hcoeff] at he
  simpa only [F, deltaDivisionIteratedRelation, Function.iterate_succ_apply',
    Function.iterate_zero_apply, relativeFreeDeltaStructure_delta_X, Nat.zero_add] using he

/-- 第2通常剰余イデアルと二段のモニックイデアルは同じ通常射を消す。 -/
theorem deltaDivisionSecondResidue_monic_le_ker_iff
    {B : Type w} [CommRing B] (D : DeltaStructure p A) (d : A) (a : σ → A)
    (u : Aˣ) (hu : (u : A) = D.delta d)
    (q : RelativeFreeDeltaRing (R := A) σ →+* B) :
    deltaDivisionSecondResidueIdeal D d a ≤ RingHom.ker q ↔
      deltaDivisionSecondMonicIdeal D d a u ≤ RingHom.ker q := by
  rw [deltaDivisionSecondResidueIdeal_eq_first_sup, deltaDivisionSecondMonicIdeal,
    ← deltaDivisionFirstResidueIdeal_eq_monic D d a u hu, sup_le_iff, sup_le_iff]
  constructor
  · rintro ⟨hfirst, hsecond⟩
    obtain ⟨hp, hd, h01⟩ := (deltaDivisionFirstResidueIdeal_le_ker_iff D d a q).mp hfirst
    refine ⟨hfirst, Ideal.span_le.mpr ?_⟩
    rintro _ ⟨s, rfl⟩
    have h2 : q (deltaDivisionIteratedRelation D d a s 2) = 0 :=
      hsecond (Ideal.subset_span (Set.mem_range_self s))
    have hpow := (deltaDivisionSecondIteratedRelation_vanish_iff_root D d a u hu q hp hd s
      (h01 s).1 (h01 s).2).mp h2
    change q (_ - _) = 0
    rw [map_sub, map_pow, hpow, sub_self]
  · rintro ⟨hfirst, hsecond⟩
    obtain ⟨hp, hd, h01⟩ := (deltaDivisionFirstResidueIdeal_le_ker_iff D d a q).mp hfirst
    refine ⟨hfirst, Ideal.span_le.mpr ?_⟩
    rintro _ ⟨s, rfl⟩
    have hm := hsecond (Ideal.subset_span (Set.mem_range_self s))
    change q (_ - _) = 0 at hm
    have hpow : q (MvPolynomial.X (s, 1)) ^ p =
        q (MvPolynomial.C (deltaDivisionSecondPowerCoefficient D a d u s)) := by
      simpa only [map_sub, map_pow, sub_eq_zero] using hm
    exact (deltaDivisionSecondIteratedRelation_vanish_iff_root D d a u hu q hp hd s
      (h01 s).1 (h01 s).2).mpr hpow

/-- 実際の第2剰余イデアルは二つのモニック冪関係式の通常イデアル。 -/
theorem deltaDivisionSecondResidueIdeal_eq_monic
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) :
    deltaDivisionSecondResidueIdeal D d a = deltaDivisionSecondMonicIdeal D d a u := by
  apply le_antisymm
  · have h : deltaDivisionSecondMonicIdeal D d a u ≤
        RingHom.ker (Ideal.Quotient.mk (deltaDivisionSecondMonicIdeal D d a u)) :=
      fun x hx => Ideal.Quotient.eq_zero_iff_mem.mpr hx
    have he := (deltaDivisionSecondResidue_monic_le_ker_iff D d a u hu _).mpr h
    exact fun x hx => Ideal.Quotient.eq_zero_iff_mem.mp (he hx)
  · have h : deltaDivisionSecondResidueIdeal D d a ≤
        RingHom.ker (Ideal.Quotient.mk (deltaDivisionSecondResidueIdeal D d a)) :=
      fun x hx => Ideal.Quotient.eq_zero_iff_mem.mpr hx
    have he := (deltaDivisionSecondResidue_monic_le_ker_iff D d a u hu _).mp h
    exact fun x hx => Ideal.Quotient.eq_zero_iff_mem.mp (he hx)

/-- 実際の第2通常商と二段のモニック関係式商の標準同型。 -/
def deltaDivisionSecondResidueMonicEquiv
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) :
    (RelativeFreeDeltaRing (R := A) σ ⧸ deltaDivisionSecondResidueIdeal D d a) ≃+*
      (RelativeFreeDeltaRing (R := A) σ ⧸ deltaDivisionSecondMonicIdeal D d a u) :=
  Ideal.quotEquivOfEq (deltaDivisionSecondResidueIdeal_eq_monic D d a u hu)

/-- 二段のモニック商同型は標準商射と両立する。 -/
@[simp] theorem deltaDivisionSecondResidueMonicEquiv_mk
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d)
    (x : RelativeFreeDeltaRing (R := A) σ) :
    deltaDivisionSecondResidueMonicEquiv D d a u hu
      (Ideal.Quotient.mk (deltaDivisionSecondResidueIdeal D d a) x) =
      Ideal.Quotient.mk (deltaDivisionSecondMonicIdeal D d a u) x :=
  Ideal.quotEquivOfEq_mk _ x

end SerrePositivity.BhattScholze

end DeltaDivisionSecondMonicPresentation

/-! ## 第2通常δ剰余を係数とする後続多項式表示

二つのモニック方程式を有限初期変数の係数イデアルへ移す。
この係数商と同時根添加環の比較は別工程。
-/

@[expose] public noncomputable section DeltaDivisionSecondPowerPresentation

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 二つの初期変数のみの多項式環に置いた係数・モニック関係式のイデアル。 -/
def deltaDivisionSecondPolynomialIdeal (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :
    Ideal (MvPolynomial (σ × Fin 2) A) :=
  ((Ideal.span {(p : MvPolynomial (σ × Fin 2) A), MvPolynomial.C d} ⊔
    Ideal.span (Set.range fun s => MvPolynomial.C (a s))) ⊔
    Ideal.span (Set.range fun s => MvPolynomial.X (s, 0) ^ p -
      MvPolynomial.C ((u⁻¹ : Aˣ) * D.delta (a s)))) ⊔
    Ideal.span (Set.range fun s => MvPolynomial.X (s, 1) ^ p -
      MvPolynomial.C (deltaDivisionSecondPowerCoefficient D a d u s))

/-- 第0変数の有限分離像。 -/
@[simp] theorem relativeFreeFiniteVariableSplitAlgEquiv_two_zero (s : σ) :
    relativeFreeFiniteVariableSplitAlgEquiv 2 σ A (MvPolynomial.X (s, 0)) =
      MvPolynomial.C (MvPolynomial.X (s, (0 : Fin 2))) :=
  relativeFreeFiniteVariableSplitAlgEquiv_X_initial 2 σ A s 0

/-- 第1変数の有限分離像。 -/
@[simp] theorem relativeFreeFiniteVariableSplitAlgEquiv_two_one (s : σ) :
    relativeFreeFiniteVariableSplitAlgEquiv 2 σ A (MvPolynomial.X (s, 1)) =
      MvPolynomial.C (MvPolynomial.X (s, (1 : Fin 2))) :=
  relativeFreeFiniteVariableSplitAlgEquiv_X_initial 2 σ A s 1

/-- 第2モニックイデアルは有限初期係数イデアルの延長へ送られる。 -/
theorem deltaDivisionSecondMonicIdeal_map_split
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :
    (deltaDivisionSecondMonicIdeal D d a u).map
      (relativeFreeFiniteVariableSplitAlgEquiv 2 σ A).toRingHom =
      (deltaDivisionSecondPolynomialIdeal D d a u).map
        (MvPolynomial.C : MvPolynomial (σ × Fin 2) A →+*
          MvPolynomial (σ × ℕ) (MvPolynomial (σ × Fin 2) A)) := by
  simp only [deltaDivisionSecondMonicIdeal, deltaDivisionFirstMonicIdeal,
    deltaDivisionSecondPolynomialIdeal, Ideal.map_sup, Ideal.map_span,
    Set.image_pair, ← Set.range_comp']
  simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, AlgEquiv.coe_toRingEquiv,
    map_natCast, relativeFreeFiniteVariableSplitAlgEquiv_C,
    relativeFreeFiniteVariableSplitAlgEquiv_two_zero,
    relativeFreeFiniteVariableSplitAlgEquiv_two_one,
    map_sub, map_pow]

/-- 実際の第2通常剰余イデアルは係数イデアルの延長へ送られる。 -/
theorem deltaDivisionSecondResidueIdeal_map_split
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) :
    (deltaDivisionSecondResidueIdeal D d a).map
      (relativeFreeFiniteVariableSplitAlgEquiv 2 σ A).toRingHom =
      (deltaDivisionSecondPolynomialIdeal D d a u).map
        (MvPolynomial.C : MvPolynomial (σ × Fin 2) A →+*
          MvPolynomial (σ × ℕ) (MvPolynomial (σ × Fin 2) A)) := by
  rw [deltaDivisionSecondResidueIdeal_eq_monic D d a u hu,
    deltaDivisionSecondMonicIdeal_map_split]

/-- 実際の第2通常δ剰余は、有限初期多項式商上の後続変数の多項式環。 -/
def deltaDivisionSecondResiduePolynomialEquiv
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) :
    (RelativeFreeDeltaRing (R := A) σ ⧸ deltaDivisionSecondResidueIdeal D d a) ≃+*
      MvPolynomial (σ × ℕ)
        (MvPolynomial (σ × Fin 2) A ⧸ deltaDivisionSecondPolynomialIdeal D d a u) :=
  (Ideal.quotientEquiv _ _ (relativeFreeFiniteVariableSplitAlgEquiv 2 σ A).toRingEquiv
    (deltaDivisionSecondResidueIdeal_map_split D d a u hu).symm).trans
    (MvPolynomial.quotientEquivQuotientMvPolynomial
      (σ := σ × ℕ) (deltaDivisionSecondPolynomialIdeal D d a u)).symm.toRingEquiv

/-- 第2後続多項式表示は標準商射と係数の商写像に両立する。 -/
theorem deltaDivisionSecondResiduePolynomialEquiv_mk
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d)
    (x : RelativeFreeDeltaRing (R := A) σ) :
    deltaDivisionSecondResiduePolynomialEquiv D d a u hu
      (Ideal.Quotient.mk (deltaDivisionSecondResidueIdeal D d a) x) =
      MvPolynomial.map (Ideal.Quotient.mk (deltaDivisionSecondPolynomialIdeal D d a u))
        (relativeFreeFiniteVariableSplitAlgEquiv 2 σ A x) := by
  change MvPolynomial.eval₂Hom
    (MvPolynomial.C.comp (Ideal.Quotient.mk (deltaDivisionSecondPolynomialIdeal D d a u)))
    MvPolynomial.X (relativeFreeFiniteVariableSplitAlgEquiv 2 σ A x) = _
  rw [MvPolynomial.map_eq_eval₂Hom_C_comp]

/-- 両初期変数は有限係数商の指定変数となる。 -/
@[simp] theorem deltaDivisionSecondResiduePolynomialEquiv_initial
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d)
    (s : σ) (i : Fin 2) :
    deltaDivisionSecondResiduePolynomialEquiv D d a u hu
      (Ideal.Quotient.mk (deltaDivisionSecondResidueIdeal D d a) (MvPolynomial.X (s, i.val))) =
      MvPolynomial.C (Ideal.Quotient.mk (deltaDivisionSecondPolynomialIdeal D d a u)
        (MvPolynomial.X (s, i))) := by
  rw [deltaDivisionSecondResiduePolynomialEquiv_mk,
    relativeFreeFiniteVariableSplitAlgEquiv_X_initial, MvPolynomial.map_C]

/-- 第2段以降の変数は外側の自由変数となる。 -/
@[simp] theorem deltaDivisionSecondResiduePolynomialEquiv_tail
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d)
    (s : σ) (n : ℕ) :
    deltaDivisionSecondResiduePolynomialEquiv D d a u hu
      (Ideal.Quotient.mk (deltaDivisionSecondResidueIdeal D d a) (MvPolynomial.X (s, n + 2))) =
      MvPolynomial.X (s, n) := by
  rw [deltaDivisionSecondResiduePolynomialEquiv_mk,
    relativeFreeFiniteVariableSplitAlgEquiv_X_tail, MvPolynomial.map_X]

/-- 元の係数は有限係数商の標準像となる。 -/
@[simp] theorem deltaDivisionSecondResiduePolynomialEquiv_coeff
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d)
    (r : A) :
    deltaDivisionSecondResiduePolynomialEquiv D d a u hu
      (Ideal.Quotient.mk (deltaDivisionSecondResidueIdeal D d a) (MvPolynomial.C r)) =
      MvPolynomial.C (Ideal.Quotient.mk (deltaDivisionSecondPolynomialIdeal D d a u)
        (MvPolynomial.C r)) := by
  rw [deltaDivisionSecondResiduePolynomialEquiv_mk,
    relativeFreeFiniteVariableSplitAlgEquiv_C, MvPolynomial.map_C]

end SerrePositivity.BhattScholze

end DeltaDivisionSecondPowerPresentation
