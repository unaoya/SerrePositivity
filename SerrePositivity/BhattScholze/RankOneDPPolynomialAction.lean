module

public import SerrePositivity.BhattScholze.RankOneDPTruncatedFree

/-! # 多項式作用と切断多項式作用の実因子化

テンソルとTorで使う多項式環の作用を指定した実環射で明示する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable {A : Type u} [CommRing A]
local notation "DA" => DividedPowerAlgebra A A

/-- 多項式変数を一次分冪生成元へ送る実A代数射。 -/
def rankOneDPPolynomialMap (A : Type u) [CommRing A] : Polynomial A →ₐ[A] DividedPowerAlgebra A A :=
  Polynomial.aeval (DividedPowerAlgebra.dp A 1 (1 : A))

/-- 指定された実多項式射の変数上の式。 -/
theorem rankOneDPPolynomialMap_X :
    rankOneDPPolynomialMap A Polynomial.X = DividedPowerAlgebra.dp A 1 (1 : A) :=
  Polynomial.aeval_X _

/-- 指定された実多項式射の係数上の式。 -/
theorem rankOneDPPolynomialMap_C (a : A) :
    rankOneDPPolynomialMap A (Polynomial.C a) = algebraMap A DA a :=
  Polynomial.aeval_C _ _

/-- 指定された多項式射による具体的スカラー作用。 -/
abbrev rankOneDPPolynomialAlgebra (A : Type u) [CommRing A] :
    Algebra (Polynomial A) (DividedPowerAlgebra A A) :=
  (rankOneDPPolynomialMap A).toRingHom.toAlgebra

/-- 指定された多項式作用と元の係数作用の実スカラー塔。 -/
theorem rankOneDPPolynomial_isScalarTower :
    letI : Algebra (Polynomial A) DA := rankOneDPPolynomialAlgebra A
    IsScalarTower A (Polynomial A) DA := by
  let : Algebra (Polynomial A) DA := rankOneDPPolynomialAlgebra A
  exact IsScalarTower.of_algebraMap_eq (fun a ↦ (rankOneDPPolynomialMap A).commutes a |>.symm)

/-- 実商写像mkによる、切断多項式環の具体的な多項式環上の代数構造。 -/
abbrev rankOneDPPolynomialQuotientAlgebra (p : ℕ) (A : Type u) [CommRing A] :
    Algebra (Polynomial A) (AdjoinRoot ((Polynomial.X : Polynomial A) ^ p)) :=
  (AdjoinRoot.mk ((Polynomial.X : Polynomial A) ^ p)).toAlgebra

/-- 実商写像による切断多項式作用も元の係数作用と可換。 -/
theorem rankOneDPPolynomialQuotient_isScalarTower (p : ℕ) :
    letI : Algebra (Polynomial A) (AdjoinRoot ((Polynomial.X : Polynomial A) ^ p)) :=
      rankOneDPPolynomialQuotientAlgebra p A
    IsScalarTower A (Polynomial A) (AdjoinRoot ((Polynomial.X : Polynomial A) ^ p)) := by
  let : Algebra (Polynomial A) (AdjoinRoot ((Polynomial.X : Polynomial A) ^ p)) :=
    rankOneDPPolynomialQuotientAlgebra p A
  exact IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)

/-- 元の多項式作用は、実商写像と切断多項式作用の合成そのもの。 -/
theorem rankOneDPPolynomial_truncated_comp {p : ℕ} (hpos : 0 < p) (hp : (p : A) = 0) :
    (rankOneDPTruncatedMap hpos hp).toRingHom.comp
        (AdjoinRoot.mk ((Polynomial.X : Polynomial A) ^ p)) =
      (rankOneDPPolynomialMap A).toRingHom := by
  apply RingHom.ext
  intro f
  exact AdjoinRoot.lift_mk (i := algebraMap A DA) (a := DividedPowerAlgebra.dp A 1 (1 : A))
    (by
      rw [Polynomial.eval₂_pow, Polynomial.eval₂_X]
      exact rankOneDPGenerator_pow_eq_zero hpos hp) f

/-- 多項式作用、実切断多項式作用、分冪代数の間の実スカラー塔。 -/
theorem rankOneDPPolynomial_truncated_isScalarTower {p : ℕ} (hpos : 0 < p) (hp : (p : A) = 0) :
    letI : Algebra (Polynomial A) DA := rankOneDPPolynomialAlgebra A
    letI : Algebra (Polynomial A) (AdjoinRoot ((Polynomial.X : Polynomial A) ^ p)) :=
      rankOneDPPolynomialQuotientAlgebra p A
    letI : Algebra (AdjoinRoot ((Polynomial.X : Polynomial A) ^ p)) DA :=
      rankOneDPTruncatedAlgebra hpos hp
    IsScalarTower (Polynomial A) (AdjoinRoot ((Polynomial.X : Polynomial A) ^ p)) DA := by
  let : Algebra (Polynomial A) DA := rankOneDPPolynomialAlgebra A
  let : Algebra (Polynomial A) (AdjoinRoot ((Polynomial.X : Polynomial A) ^ p)) :=
    rankOneDPPolynomialQuotientAlgebra p A
  let : Algebra (AdjoinRoot ((Polynomial.X : Polynomial A) ^ p)) DA :=
    rankOneDPTruncatedAlgebra hpos hp
  exact IsScalarTower.of_algebraMap_eq
    (fun f ↦ (RingHom.congr_fun (rankOneDPPolynomial_truncated_comp hpos hp) f).symm)

end SerrePositivity.BhattScholze
