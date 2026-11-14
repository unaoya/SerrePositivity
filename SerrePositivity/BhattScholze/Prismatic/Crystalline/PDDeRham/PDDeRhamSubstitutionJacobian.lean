module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDRawPolynomialSubstitution
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamColumn

/-!
# 分冪 de Rham の多項式代入の Jacobian

## 概要
各頂点の多項式代入の微分を、分冪座標の偏微分から作る。

## 方針
頂点の生成元の像を微分し、差座標では両頂点の結果の差を取る。

## 規約
係数は標的の未完備分冪環に取る。

## 使われ方
完備化の前に多項式代入と縦微分との可換性を調べる。
-/

public noncomputable section

open CategoryTheory
open scoped Simplicial TensorProduct

universe u

namespace SerrePositivity.BhattScholze.Prismatic.PDRawPolynomialSubstitution

variable {k : Type u} [CommRing k] {Q Q' : Poly k} (f : Q ⟶ Q')

/-- 指定した頂点での多項式の微分の各分冪座標成分。 -/
def vertexPartial (n : ℕ) (i : Fin (n + 1)) (a : pdCoordinates Q'.n n) :
    MvPolynomial (Fin Q.n) k →ₗ[k] pdRaw k Q'.n n :=
  (pdRawPartial k Q'.n n a).comp
    ((evalVertex (Q := Q') n i).comp (Poly.hom f)).toLinearMap

theorem vertexPartial_mul (n : ℕ) (i : Fin (n + 1)) (a : pdCoordinates Q'.n n)
    (x y : MvPolynomial (Fin Q.n) k) :
    vertexPartial f n i a (x * y) =
      evalVertex (Q := Q') n i (Poly.hom f x) * vertexPartial f n i a y +
      evalVertex (Q := Q') n i (Poly.hom f y) * vertexPartial f n i a x := by
  let e := (evalVertex (Q := Q') n i).comp (Poly.hom f)
  change pdRawPartial k Q'.n n a (e (x * y)) =
    e x * pdRawPartial k Q'.n n a (e y) + e y * pdRawPartial k Q'.n n a (e x)
  rw [map_mul, ← pdRawDerivation_toLinearMap]
  exact (pdRawDerivation k Q'.n n a).leibniz' (e x) (e y)

/-- 第 0 頂点と差座標の基底で表した多項式代入の Jacobian。 -/
def jacobian (n : ℕ) (b : pdCoordinates Q'.n n) :
    pdCoordinates Q.n n → pdRaw k Q'.n n
  | .inl j => vertexPartial f n 0 b (MvPolynomial.X j)
  | .inr (j, i) =>
      vertexPartial f n i.succ b (MvPolynomial.X j) - vertexPartial f n 0 b (MvPolynomial.X j)

/-- コピーの微分形式を標的の係数つきの 1 形式へ送る。 -/
def jacobianOnCopies (n : ℕ) :
    ((Fin Q.n × Fin (n + 1)) →₀ k) →ₗ[k]
      pdRaw k Q'.n n ⊗[k] ((Fin Q'.n × Fin (n + 1)) →₀ k) :=
  Finsupp.linearCombination k fun ji =>
    ∑ b : pdCoordinates Q'.n n,
      vertexPartial f n ji.2 b (MvPolynomial.X ji.1) ⊗ₜ[k] pdCoordinateBasis k Q'.n ⦋n⦌ b

theorem jacobianOnCopies_single (n : ℕ) (j : Fin Q.n) (i : Fin (n + 1)) :
    jacobianOnCopies f n (Finsupp.single (j, i) 1) =
      ∑ b : pdCoordinates Q'.n n,
        vertexPartial f n i b (MvPolynomial.X j) ⊗ₜ[k] pdCoordinateBasis k Q'.n ⦋n⦌ b := by
  rw [jacobianOnCopies, Finsupp.linearCombination_single, one_smul]

end SerrePositivity.BhattScholze.Prismatic.PDRawPolynomialSubstitution
