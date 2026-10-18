module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleLeibnizZero
public import Mathlib.LinearAlgebra.BilinearMap

/-!
# 正規化鎖上の shuffle の Leibniz 則

概要：Berger–Fresse §1.1.3 の生成元上の shuffle の微分公式を任意の正規化鎖へ拡張する。
方針：二つの入力に関する線形写像の外延性を正規化生成元に順に適用する。
規約：正次数の二入力では第一の微分項の次数移送と第二の微分項の Koszul 符号を明示する。
使われ方：shuffle の部分合成を複体の射へまとめるための微分の両立性を与える。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory
open scoped Simplicial

variable (A : Type u) [CommRing A]

/-- 概要：正規化生成元上の一致で双線形写像を判定する（Berger–Fresse §1.1.3）。
方針：正規化生成元による射の外延性を第一の入力と第二の入力に順に適用する。
規約：出力は任意の A 加群でよい。
使われ方：生成元上の微分の等式を任意の鎖へ拡張する。 -/
lemma normalizedGenerator_bilinear_ext (m n p q : ℕ) {M : ModuleCat.{u} A}
    (f g : (normalizedChains A m).X p →ₗ[A] (normalizedChains A n).X q →ₗ[A] M)
    (h : ∀ x : (simplicial m) _⦋p⦌, ∀ y : (simplicial n) _⦋q⦌,
      f (normalizedGenerator A m p x) (normalizedGenerator A n q y) =
        g (normalizedGenerator A m p x) (normalizedGenerator A n q y)) : f = g := by
  have hfg : ModuleCat.ofHom f = ModuleCat.ofHom g := by
    apply normalizedGenerator_hom_ext A m p
    intro x
    have hxy : ModuleCat.ofHom (f (normalizedGenerator A m p x)) =
        ModuleCat.ofHom (g (normalizedGenerator A m p x)) := by
      apply normalizedGenerator_hom_ext A n q
      exact h x
    exact congrArg (fun z => z.hom) hxy
  exact congrArg (fun z => z.hom) hfg

/-- 概要：正次数の任意の正規化鎖に対して shuffle は Leibniz 則を満たす（Berger–Fresse §1.1.3）。
方針：微分後の shuffle と二つの微分項を双線形写像として比較し、生成元上の定理を使う。
規約：第一の微分項を共通の出力次数へ移し、第二の項に (−1)^(p+1) を掛ける。
使われ方：二つの入力が正次数の場合の鎖写像の条件となる。 -/
lemma shuffleBilinear_d_positive (m n : ℕ) (i : Fin (m + 1)) (p q : ℕ)
    (x : (normalizedChains A (m + 1)).X (p + 1))
    (y : (normalizedChains A n).X (q + 1)) :
    (normalizedChains A (m + n)).d (p + 1 + (q + 1)) (p + 1 + q)
        (shuffleBilinear A m n i (p + 1) (q + 1) x y) =
      degreeTransport A (m + n) (by omega : p + (q + 1) = p + 1 + q)
        (shuffleBilinear A m n i p (q + 1)
          ((normalizedChains A (m + 1)).d (p + 1) p x) y) +
      (-1 : ℤ) ^ (p + 1) • shuffleBilinear A m n i (p + 1) q x
        ((normalizedChains A n).d (q + 1) q y) := by
  let L := (shuffleBilinear A m n i (p + 1) (q + 1)).compr₂
    ((normalizedChains A (m + n)).d (p + 1 + (q + 1)) (p + 1 + q)).hom
  let R := (((shuffleBilinear A m n i p (q + 1)).comp
      ((normalizedChains A (m + 1)).d (p + 1) p).hom).compr₂
        (degreeTransport A (m + n) (by omega : p + (q + 1) = p + 1 + q))) +
    (-1 : ℤ) ^ (p + 1) • (shuffleBilinear A m n i (p + 1) q).compl₂
      ((normalizedChains A n).d (q + 1) q).hom
  have hLR : L = R := by
    apply normalizedGenerator_bilinear_ext A (m + 1) n (p + 1) (q + 1)
    intro sx sy
    simp only [L, R, LinearMap.compr₂_apply, LinearMap.comp_apply, LinearMap.compl₂_apply,
      LinearMap.add_apply, LinearMap.smul_apply, shuffleBilinear_generators]
    exact shuffleValue_d_positive A m n i p q sx sy
  exact congrArg (fun f => f x y) hLR

/-- 概要：次数0の第一の鎖と任意の第二の鎖について shuffle は微分と可換する（Berger–Fresse §1.1.3）。
方針：両辺を双線形写像として比較し、第一の入力が次数0の生成元の公式を使う。
規約：第二の入力の次数は q+1 である。
使われ方：第一の入力が次数0の場合の鎖写像の条件となる。 -/
lemma shuffleBilinear_d_leftZero (m n : ℕ) (i : Fin (m + 1)) (q : ℕ)
    (x : (normalizedChains A (m + 1)).X 0) (y : (normalizedChains A n).X (q + 1)) :
    (normalizedChains A (m + n)).d (0 + (q + 1)) (0 + q)
        (shuffleBilinear A m n i 0 (q + 1) x y) =
      shuffleBilinear A m n i 0 q x ((normalizedChains A n).d (q + 1) q y) := by
  let L := (shuffleBilinear A m n i 0 (q + 1)).compr₂
    ((normalizedChains A (m + n)).d (0 + (q + 1)) (0 + q)).hom
  let R := (shuffleBilinear A m n i 0 q).compl₂ ((normalizedChains A n).d (q + 1) q).hom
  have hLR : L = R := by
    apply normalizedGenerator_bilinear_ext A (m + 1) n 0 (q + 1)
    intro sx sy
    simp only [L, R, LinearMap.compr₂_apply, LinearMap.compl₂_apply, shuffleBilinear_generators]
    exact shuffleValue_d_leftZero A m n i q sx sy
  exact congrArg (fun f => f x y) hLR

/-- 概要：任意の第一の鎖と次数0の第二の鎖について shuffle は微分と可換する（Berger–Fresse §1.1.3）。
方針：両辺を双線形写像として比較し、第二の入力が次数0の生成元の公式を使う。
規約：第一の入力の次数は p+1 である。
使われ方：第二の入力が次数0の場合の鎖写像の条件となる。 -/
lemma shuffleBilinear_d_rightZero (m n : ℕ) (i : Fin (m + 1)) (p : ℕ)
    (x : (normalizedChains A (m + 1)).X (p + 1)) (y : (normalizedChains A n).X 0) :
    (normalizedChains A (m + n)).d (p + 1 + 0) (p + 0)
        (shuffleBilinear A m n i (p + 1) 0 x y) =
      shuffleBilinear A m n i p 0 ((normalizedChains A (m + 1)).d (p + 1) p x) y := by
  let L := (shuffleBilinear A m n i (p + 1) 0).compr₂
    ((normalizedChains A (m + n)).d (p + 1 + 0) (p + 0)).hom
  let R := (shuffleBilinear A m n i p 0).comp ((normalizedChains A (m + 1)).d (p + 1) p).hom
  have hLR : L = R := by
    apply normalizedGenerator_bilinear_ext A (m + 1) n (p + 1) 0
    intro sx sy
    simp only [L, R, LinearMap.compr₂_apply, LinearMap.comp_apply, shuffleBilinear_generators]
    exact shuffleValue_d_rightZero A m n i p sx sy
  exact congrArg (fun f => f x y) hLR

end SerrePositivity.EInfinity.BarrattEccles
