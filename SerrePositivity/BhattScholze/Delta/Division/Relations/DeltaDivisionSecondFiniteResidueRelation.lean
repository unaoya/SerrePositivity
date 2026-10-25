module

public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeFiniteResidue
public import SerrePositivity.BhattScholze.Delta.Division.Relations.DeltaDivisionFiniteResidueRelation
public import SerrePositivity.BhattScholze.Delta.Division.Relations.DeltaDivisionSecondResidueRelation

/-! # 第2有限δ関係式からのモニック冪方程式

通常射が深さ0,1,2の関係式を消すことから次の変数の冪を求める。
有限段の商のδ安定性を要求しない。
-/

@[expose] public noncomputable section
universe u v w
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
