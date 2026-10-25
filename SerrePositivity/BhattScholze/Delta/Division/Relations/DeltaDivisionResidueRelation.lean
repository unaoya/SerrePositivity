module

public import SerrePositivity.BhattScholze.Delta.Division.DeltaAdjoinDivision
public import Mathlib.Algebra.Polynomial.Monic

/-! # B4-6：δ除算関係式の(p,d)剰余の最初のモニック方程式

d*x=aをδで微分し、p,dを消す通常の環射に沿って計算する。
剰余環にδ構造を要求せず、一般pねじれ・零終域も含む。
この最初の方程式だけから除算包全体の平坦性を結論しない。
-/

@[expose] public noncomputable section
universe u v w
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
