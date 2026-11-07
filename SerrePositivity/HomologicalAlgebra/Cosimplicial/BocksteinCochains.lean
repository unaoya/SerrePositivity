module

public import SerrePositivity.HomologicalAlgebra.Cosimplicial.CupCohomology
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.Quotient

/-!
# 正則元による Bockstein の余鎖計算

## 概要
商の余輪体を環に持ち上げ、余鎖微分を指定元で割る。

## 方針
指定元の自然性から、指定元による乗法は余鎖微分と可換。

## 規約
交代余面微分の最初の余面の符号は正。

## 使われ方
Bockstein の代表元公式、平方零と Leibniz 則。
-/

public section

universe u

open CategoryTheory
open scoped Simplicial

namespace SerrePositivity.Cosimplicial

variable (C : CosimplicialObject CommRingCat.{u}) (d : ∀ n : SimplexCategory, C.obj n)
  (hd_nat : ∀ {m n} (θ : m ⟶ n), C.map θ (d m) = d n)

/-- 余単体的環の射は交代余面微分と可換。 -/
theorem cochainDifferential_natural (D : CosimplicialObject CommRingCat.{u})
    (f : C ⟶ D) (n : ℕ) (x : C.obj ⦋n⦌) :
    f.app ⦋n + 1⦌ (cochainDifferential C n x) =
      cochainDifferential D n (f.app ⦋n⦌ x) := by
  rw [cochainDifferential_apply, cochainDifferential_apply]
  simp only [map_sum, map_zsmul, ← CommRingCat.comp_apply, f.naturality]

include hd_nat

/-- 自然な指定元による乗法は交代余面微分と可換。 -/
theorem cochainDifferential_mul_natural (n : ℕ) (x : C.obj ⦋n⦌) :
    cochainDifferential C n (d ⦋n⦌ * x) =
      d ⦋n + 1⦌ * cochainDifferential C n x := by
  rw [cochainDifferential_apply, cochainDifferential_apply, Finset.mul_sum]
  simp only [map_mul, hd_nat, mul_smul_comm]

omit hd_nat in
/-- 交代余面微分の合成は零。 -/
theorem cochainDifferential_sq (n : ℕ) (x : C.obj ⦋n⦌) :
    cochainDifferential C (n + 1) (cochainDifferential C n x) = 0 := by
  rw [← ringCochainComplex_d_apply, ← ringCochainComplex_d_apply]
  let hx : (ringCochainComplex C).X n := x
  change (ringCochainComplex C).d (n + 1) (n + 1 + 1)
    ((ringCochainComplex C).d n (n + 1) hx) = 0
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.d_comp_d]
  rfl

/-- 概要：商の余輪体の任意の持ち上げの微分は指定元で割り切れる。
方針：商射と微分の可換性および単項生成イデアルへの所属。
規約：商は指定元の一乗で取る。
使われ方：正則元 Bockstein の計算。 -/
theorem exists_cochainDifferential_eq_mul (n : ℕ) (x : C.obj ⦋n⦌)
    (hx : cochainDifferential (quotPow C d hd_nat 1) n
      ((quotProjection C d hd_nat 1).app ⦋n⦌ x) = 0) :
    ∃ y : C.obj ⦋n + 1⦌, cochainDifferential C n x = d ⦋n + 1⦌ * y := by
  rw [← cochainDifferential_natural C _ (quotProjection C d hd_nat 1)] at hx
  change Ideal.Quotient.mk (Ideal.span {d ⦋n + 1⦌ ^ 1}) (cochainDifferential C n x) = 0 at hx
  rw [Ideal.Quotient.eq_zero_iff_mem, pow_one, Ideal.mem_span_singleton] at hx
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, hy⟩

/-- 概要：正則元で割った持ち上げの微分は余輪体。
方針：微分の二乗が零なので、次の次数で正則性を使って指定元を消去する。
規約：余輪体であることは商を取る前に成立する。
使われ方：Bockstein の平方零。 -/
theorem cochainDifferential_eq_zero_of_eq_mul
    (hd_reg : ∀ n, Function.Injective (fun x : C.obj n => d n * x))
    (n : ℕ) (x : C.obj ⦋n⦌) (y : C.obj ⦋n + 1⦌)
    (hy : cochainDifferential C n x = d ⦋n + 1⦌ * y) :
    cochainDifferential C (n + 1) y = 0 := by
  apply hd_reg ⦋n + 1 + 1⦌
  change d ⦋n + 1 + 1⦌ * cochainDifferential C (n + 1) y = d ⦋n + 1 + 1⦌ * 0
  rw [mul_zero, ← cochainDifferential_mul_natural C d hd_nat, ← hy, cochainDifferential_sq]

omit hd_nat in
private theorem cast_mul_natural {m n : ℕ} (h : m = n) (x : C.obj ⦋m⦌) :
    cast (congrArg (fun j => (C.obj ⦋j⦌ : Type u)) h) (d ⦋m⦌ * x) =
      d ⦋n⦌ * cast (congrArg (fun j => (C.obj ⦋j⦌ : Type u)) h) x := by
  subst n
  rfl

private theorem cup_mul_natural_left {m n : ℕ} (x : C.obj ⦋m⦌) (y : C.obj ⦋n⦌) :
    cup C (d ⦋m⦌ * x) y = d ⦋m + n⦌ * cup C x y := by
  simp only [cup, map_mul, hd_nat, mul_assoc]

private theorem cup_mul_natural_right {m n : ℕ} (x : C.obj ⦋m⦌) (y : C.obj ⦋n⦌) :
    cup C x (d ⦋n⦌ * y) = d ⦋m + n⦌ * cup C x y := by
  simp only [cup, map_mul, hd_nat]
  ac_rfl

/-- 概要：積の持ち上げの微分を指定元で割ると、二つの持ち上げの商の Leibniz 式になる。
方針：余鎖の Leibniz 則に二つの因数分解を代入し、指定元をくくる。
規約：左因子の次数 m に応じて右因子側に (−1)^m を掛ける。
使われ方：コホモロジー上の Bockstein の Leibniz 則。 -/
theorem cochainDifferential_cup_of_eq_mul {m n : ℕ} (x : C.obj ⦋m⦌) (y : C.obj ⦋n⦌)
    (a : C.obj ⦋m + 1⦌) (b : C.obj ⦋n + 1⦌)
    (ha : cochainDifferential C m x = d ⦋m + 1⦌ * a)
    (hb : cochainDifferential C n y = d ⦋n + 1⦌ * b) :
    cochainDifferential C (m + n) (cup C x y) = d ⦋m + n + 1⦌ *
      (cast (congrArg (fun j => (C.obj ⦋j⦌ : Type u)) (by omega : (m + 1) + n = m + n + 1))
        (cup C a y) + (-1 : ℤ) ^ m • cup C x b) := by
  have e : (m + 1) + n = m + n + 1 := by omega
  erw [cochainDifferential_cup, ha, hb, cup_mul_natural_left C d hd_nat,
    cup_mul_natural_right C d hd_nat, cast_mul_natural C d e]
  rw [mul_add, mul_smul_comm]
  rfl

end SerrePositivity.Cosimplicial
