module

public import SerrePositivity.BhattScholze.Andre.DividedPowerPrimeFiniteTensor

/-!
# André E1・E2：有限切断テンソル段の普遍性

## 概要

有限テンソル段からの係数代数射は、p 乗が零となる n 個の元の選択と対応する。
BS Rem 7.15(1)（著者版 p.62）の切断多項式表示の有限版。

## 方針

AdjoinRoot とテンソル積の普遍性を反復し、変数上の値による外延性を示す。

## 規約

p は任意の自然数。普遍性自体には素数性・標数・非零性は不要。

## 使われ方

有限切断多項式商と有限テンソル段を同定して標準評価の単射性へ進む。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open scoped TensorProduct
variable {A : Type u} [CommRing A] (p : ℕ)
variable {B : Type u} [CommRing B] [Algebra A B]
local notation "C" => AdjoinRoot ((Polynomial.X : Polynomial A) ^ p)

/-- 概要：p 乗が零となる元の有限族への指定値から有限テンソル段の射を作る。
方針：最初の元に AdjoinRoot の普遍射、残りに帰納的な普遍射を使いテンソルから延長する。
規約：全射性や単射性をこの射の前提にしない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の切断変数の普遍性。 -/
def dividedPowerPrimeTensorStageLift : (n : ℕ) → (b : Fin n → B) →
    (∀ i, b i ^ p = 0) → dividedPowerPrimeTensorStage (A := A) p n →ₐ[A] B
  | 0, _, _ => Algebra.ofId A B
  | n + 1, b, hb => Algebra.TensorProduct.lift
      (AdjoinRoot.liftAlgHom ((Polynomial.X : Polynomial A) ^ p) (Algebra.ofId A B)
        (b 0) (by simpa only [Polynomial.eval₂_pow, Polynomial.eval₂_X] using hb 0))
      (dividedPowerPrimeTensorStageLift n (fun i => b i.succ) (fun i => hb i.succ))
      (fun _ _ => Commute.all _ _)

/-- 概要：有限テンソル段の普遍射は各変数を指定した元へ送る。
方針：純テンソルの評価と AdjoinRoot の根の評価を帰納する。
規約：変数の番号を保持する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の多項式表示の逆射。 -/
theorem dividedPowerPrimeTensorStageLift_root (n : ℕ) (b : Fin n → B)
    (hb : ∀ i, b i ^ p = 0) (i : Fin n) :
    dividedPowerPrimeTensorStageLift (A := A) p n b hb
      (dividedPowerPrimeTensorStageRoot (A := A) p n i) =
      b i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    let f0 : C →ₐ[A] B := AdjoinRoot.liftAlgHom ((Polynomial.X : Polynomial A) ^ p)
      (Algebra.ofId A B) (b 0)
      (by simpa only [Polynomial.eval₂_pow, Polynomial.eval₂_X] using hb 0)
    let f1 := dividedPowerPrimeTensorStageLift (A := A) p n
      (fun j => b j.succ) (fun j => hb j.succ)
    refine Fin.cases ?_ (fun j => ?_) i
    · change f0 (AdjoinRoot.root ((Polynomial.X : Polynomial A) ^ p)) * f1 1 = b 0
      rw [map_one, mul_one]
      exact AdjoinRoot.lift_root (i := algebraMap A B)
        (by simpa only [Polynomial.eval₂_pow, Polynomial.eval₂_X] using hb 0)
    · change f0 1 * f1 (dividedPowerPrimeTensorStageRoot (A := A) p n j) = b j.succ
      rw [map_one, one_mul]
      exact ih _ _ j

/-- 概要：有限テンソル段からの係数代数射は全変数上の値で一意に決まる。
方針：左因子では根の外延性、右因子では前段の変数の外延性を使う。
規約：終域は任意の可換係数代数。
使われ方：BS Rem 7.15(1)（著者版 p.62）の有限切断表示の同型の検証。 -/
theorem dividedPowerPrimeTensorStageHom_ext (n : ℕ)
    (f g : dividedPowerPrimeTensorStage (A := A) p n →ₐ[A] B)
    (h : ∀ i, f (dividedPowerPrimeTensorStageRoot (A := A) p n i) =
      g (dividedPowerPrimeTensorStageRoot (A := A) p n i)) : f = g := by
  induction n with
  | zero =>
    apply AlgHom.ext
    intro a
    exact (f.commutes a).trans (g.commutes a).symm
  | succ n ih =>
    apply Algebra.TensorProduct.ext
    · apply AdjoinRoot.algHom_ext
      exact h 0
    · apply ih
      intro i
      exact h i.succ

end SerrePositivity.BhattScholze.Andre
