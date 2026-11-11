module

public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
概要：標準 étale 整域は、指定座標が生成する一変数の多項式商と同じ分数体を持つ。
方針：標準 étale 表示で座標の多項式となる分子と分母を取り出し、評価写像の核を最小多項式で表す。
規約：多項式商を最小多項式で与えるときは係数環を整閉整域とする。
使われ方：滑らかな生成ファイバーを超曲面模型と比較する。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped Polynomial

/--
概要：標準 étale 表示の座標が生成する分数体内の部分代数は、元の整域と同じ分数体を持つ。
方針：標準 étale 表示の局所化の分母を、分数の分子と分母に共通の冪を掛けて払う。
規約：部分代数は座標で評価する多項式環の像として表す。
使われ方：超曲面模型が同じ関数体を持つことの証明。
-/
theorem isFractionRing_aeval_range_of_standardEtalePresentation
    {R C L : Type*} [CommRing R] [CommRing C] [IsDomain C] [Algebra R C]
    [Field L] [Algebra C L] [Algebra R L] [IsScalarTower R C L] [IsFractionRing C L]
    (P : StandardEtalePresentation R C) :
    IsFractionRing (Polynomial.aeval (R := R) (algebraMap C L P.x)).range L := by
  let i := IsScalarTower.toAlgHom R C L
  let v : R[X] →ₐ[R] L := Polynomial.aeval (i P.x)
  let D := v.range
  have hEval (p : R[X]) : i (Polynomial.aeval P.x p) = v p :=
    (Polynomial.aeval_algHom_apply i P.x p).symm
  let d := v P.g
  have hd : d ≠ 0 := by
    change v P.g ≠ 0
    rw [← hEval]
    exact (P.hasMap.2.map i).ne_zero
  apply IsFractionRing.of_field
  intro z
  obtain ⟨a, b, _, hz⟩ := IsFractionRing.div_surjective C z
  obtain ⟨p, m, hp⟩ := P.exists_mul_aeval_x_g_pow_eq_aeval_x a
  obtain ⟨q, n, hq⟩ := P.exists_mul_aeval_x_g_pow_eq_aeval_x b
  have hp' : i a * d ^ m = v p := by
    change i a * v P.g ^ m = v p
    rw [← hEval P.g, ← hEval p, ← map_pow, ← map_mul, hp]
  have hq' : i b * d ^ n = v q := by
    change i b * v P.g ^ n = v q
    rw [← hEval P.g, ← hEval q, ← map_pow, ← map_mul, hq]
  let x : D := ⟨v (p * P.g ^ n), ⟨_, rfl⟩⟩
  let y : D := ⟨v (q * P.g ^ m), ⟨_, rfl⟩⟩
  refine ⟨x, y, ?_⟩
  change z = v (p * P.g ^ n) / v (q * P.g ^ m)
  rw [map_mul, map_mul, map_pow, map_pow, ← hp', ← hq']
  calc
    z = i a / i b := hz.symm
    _ = i a * (d ^ m * d ^ n) / (i b * (d ^ m * d ^ n)) :=
      (mul_div_mul_right _ _ (mul_ne_zero (pow_ne_zero _ hd) (pow_ne_zero _ hd))).symm
    _ = _ := by rw [mul_assoc, mul_assoc, mul_comm (d ^ n) (d ^ m)]

/--
概要：整閉整域上の標準 étale 表示の座標が生成する部分代数は、最小多項式による根添加と同型。
方針：座標への評価写像の核を最小多項式の生成するイデアルとして計算する。
規約：座標は元の整域の分数体への像で取る。
使われ方：標準 étale チャートの超曲面模型。
-/
def adjoinRootMinpolyEquiv_aeval_range_of_standardEtalePresentation
    {R C L : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing C] [IsDomain C] [Algebra R C] [Field L] [Algebra C L]
    [Algebra R L] [IsScalarTower R C L] [Module.IsTorsionFree R L]
    (P : StandardEtalePresentation R C) :
    AdjoinRoot (minpoly R (algebraMap C L P.x)) ≃ₐ[R]
      (Polynomial.aeval (R := R) (algebraMap C L P.x)).range := by
  let i := IsScalarTower.toAlgHom R C L
  have h : IsIntegral R (i P.x) :=
    (show IsIntegral R P.x from ⟨P.f, P.monic_f, P.hasMap.1⟩).map i
  let v : R[X] →ₐ[R] L := Polynomial.aeval (i P.x)
  exact (Ideal.quotientEquivAlgOfEq R (minpoly.ker_eval h).symm).trans
    (Ideal.quotientKerEquivRange v)

end SerrePositivity.AlgebraicGeometry
