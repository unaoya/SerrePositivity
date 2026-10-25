module

public import SerrePositivity.BhattScholze.Delta.Division.Relations.DeltaDivisionResidueRelation
public import SerrePositivity.BhattScholze.Delta.Free.Finite.DeltaResidueArithmetic

/-! # B4-6：δ除算の二段目のモニック関係式

p,dを消す射の下でδ²(d*x)を計算する。
δ²の剰余が、δ(x)のp乗を単元係数で含むことを証明する。
有限段表示全体・除算包の平坦性の証明とは区別する。
-/

@[expose] public noncomputable section
universe u v w
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
