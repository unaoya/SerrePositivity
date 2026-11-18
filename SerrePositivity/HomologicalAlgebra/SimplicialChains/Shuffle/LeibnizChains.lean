module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.LeibnizZero
public import Mathlib.LinearAlgebra.BilinearMap
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleLeibnizChains

/-!
# 一般の単体集合の正規化鎖上の shuffle の Leibniz 則

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

namespace SerrePositivity.SimplicialChains.Shuffle

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.SerrePositivity.EInfinity.BarrattEccles
open scoped _root_.Simplicial

variable (A : Type u) [CommRing A]

/-- 概要：正次数の任意の正規化鎖に対して shuffle は Leibniz 則を満たす（Berger–Fresse §1.1.3）。
方針：微分後の shuffle と二つの微分項を双線形写像として比較し、生成元上の定理を使う。
規約：第一の微分項を共通の出力次数へ移し、第二の項に (−1)^(p+1) を掛ける。
使われ方：二つの入力が正次数の場合の鎖写像の条件となる。 -/
lemma shuffleBilinear_d_positive (X Y : SSet.{0}) (p q : ℕ)
    (x : (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).X (p + 1))
    (y : (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A Y).X (q + 1)) :
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A (X ⊗ Y)).d (p + 1 + (q + 1)) (p + 1 + q)
        (_root_.SerrePositivity.SimplicialChains.Shuffle.bilinear A X Y (p + 1) (q + 1) x y) =
      _root_.SerrePositivity.SimplicialChains.Shuffle.degreeTransport A (X ⊗ Y) (by omega : p + (q + 1) = p + 1 + q)
        (_root_.SerrePositivity.SimplicialChains.Shuffle.bilinear A X Y p (q + 1)
          ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).d (p + 1) p x) y) +
      (-1 : ℤ) ^ (p + 1) • _root_.SerrePositivity.SimplicialChains.Shuffle.bilinear A X Y (p + 1) q x
        ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A Y).d (q + 1) q y) := by
  let L := (_root_.SerrePositivity.SimplicialChains.Shuffle.bilinear A X Y (p + 1) (q + 1)).compr₂
    ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A (X ⊗ Y)).d (p + 1 + (q + 1)) (p + 1 + q)).hom
  let R := (((_root_.SerrePositivity.SimplicialChains.Shuffle.bilinear A X Y p (q + 1)).comp
      ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).d (p + 1) p).hom).compr₂
        (_root_.SerrePositivity.SimplicialChains.Shuffle.degreeTransport A (X ⊗ Y) (by omega : p + (q + 1) = p + 1 + q))) +
    (-1 : ℤ) ^ (p + 1) • (_root_.SerrePositivity.SimplicialChains.Shuffle.bilinear A X Y (p + 1) q).compl₂
      ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A Y).d (q + 1) q).hom
  have hLR : L = R := by
    apply _root_.SerrePositivity.SimplicialChains.Shuffle.bilinear_hom_ext A X Y (p + 1) (q + 1)
    intro sx sy
    simp only [L, R, LinearMap.compr₂_apply, LinearMap.comp_apply, LinearMap.compl₂_apply,
      LinearMap.add_apply, LinearMap.smul_apply, _root_.SerrePositivity.SimplicialChains.Shuffle.bilinear_generators]
    exact _root_.SerrePositivity.SimplicialChains.Shuffle.shuffleValue_d_positive A X Y p q sx sy
  exact congrArg (fun f => f x y) hLR

/-- 概要：次数0の第一の鎖と任意の第二の鎖について shuffle は微分と可換する（Berger–Fresse §1.1.3）。
方針：両辺を双線形写像として比較し、第一の入力が次数0の生成元の公式を使う。
規約：第二の入力の次数は q+1 である。
使われ方：第一の入力が次数0の場合の鎖写像の条件となる。 -/
lemma shuffleBilinear_d_leftZero (X Y : SSet.{0}) (q : ℕ)
    (x : (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).X 0) (y : (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A Y).X (q + 1)) :
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A (X ⊗ Y)).d (0 + (q + 1)) (0 + q)
        (_root_.SerrePositivity.SimplicialChains.Shuffle.bilinear A X Y 0 (q + 1) x y) =
      _root_.SerrePositivity.SimplicialChains.Shuffle.bilinear A X Y 0 q x ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A Y).d (q + 1) q y) := by
  let L := (_root_.SerrePositivity.SimplicialChains.Shuffle.bilinear A X Y 0 (q + 1)).compr₂
    ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A (X ⊗ Y)).d (0 + (q + 1)) (0 + q)).hom
  let R := (_root_.SerrePositivity.SimplicialChains.Shuffle.bilinear A X Y 0 q).compl₂ ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A Y).d (q + 1) q).hom
  have hLR : L = R := by
    apply _root_.SerrePositivity.SimplicialChains.Shuffle.bilinear_hom_ext A X Y 0 (q + 1)
    intro sx sy
    simp only [L, R, LinearMap.compr₂_apply, LinearMap.compl₂_apply, _root_.SerrePositivity.SimplicialChains.Shuffle.bilinear_generators]
    exact _root_.SerrePositivity.SimplicialChains.Shuffle.shuffleValue_d_leftZero A X Y q sx sy
  exact congrArg (fun f => f x y) hLR

/-- 概要：任意の第一の鎖と次数0の第二の鎖について shuffle は微分と可換する（Berger–Fresse §1.1.3）。
方針：両辺を双線形写像として比較し、第二の入力が次数0の生成元の公式を使う。
規約：第一の入力の次数は p+1 である。
使われ方：第二の入力が次数0の場合の鎖写像の条件となる。 -/
lemma shuffleBilinear_d_rightZero (X Y : SSet.{0}) (p : ℕ)
    (x : (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).X (p + 1)) (y : (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A Y).X 0) :
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A (X ⊗ Y)).d (p + 1 + 0) (p + 0)
        (_root_.SerrePositivity.SimplicialChains.Shuffle.bilinear A X Y (p + 1) 0 x y) =
      _root_.SerrePositivity.SimplicialChains.Shuffle.bilinear A X Y p 0 ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).d (p + 1) p x) y := by
  let L := (_root_.SerrePositivity.SimplicialChains.Shuffle.bilinear A X Y (p + 1) 0).compr₂
    ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A (X ⊗ Y)).d (p + 1 + 0) (p + 0)).hom
  let R := (_root_.SerrePositivity.SimplicialChains.Shuffle.bilinear A X Y p 0).comp ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).d (p + 1) p).hom
  have hLR : L = R := by
    apply _root_.SerrePositivity.SimplicialChains.Shuffle.bilinear_hom_ext A X Y (p + 1) 0
    intro sx sy
    simp only [L, R, LinearMap.compr₂_apply, LinearMap.comp_apply, _root_.SerrePositivity.SimplicialChains.Shuffle.bilinear_generators]
    exact _root_.SerrePositivity.SimplicialChains.Shuffle.shuffleValue_d_rightZero A X Y p sx sy
  exact congrArg (fun f => f x y) hLR

end SerrePositivity.SimplicialChains.Shuffle
