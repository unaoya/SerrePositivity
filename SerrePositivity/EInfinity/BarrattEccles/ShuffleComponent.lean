module

public import SerrePositivity.EInfinity.BarrattEccles.Generators
public import SerrePositivity.EInfinity.BarrattEccles.PermutationComposition
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleSign

/-!
# shuffle 合成の次数ごとの成分

概要：Berger–Fresse §1.1.3 の経路に沿う置換列の合成と、その符号つき和を構成する。
方針：各経路で二つの置換列を退化させ、頂点ごとに部分合成して正規化する。
規約：このファイルでは次数ごとの双線形写像を構成し、鎖写像の条件は別途証明する。
使われ方：Barratt–Eccles オペラッドの複体上の部分合成の成分となる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory
open scoped Simplicial

/-- 概要：一つの shuffle 経路が定める合成置換列（Berger–Fresse §1.1.3）。
方針：経路の水平・垂直座標に従って頂点を選び、各対の置換を部分合成する。
規約：p 次元と q 次元の単体から p+q 次元の単体を得る。
使われ方：合成の shuffle 和の一項を与える。 -/
def shuffleSimplex (m n : ℕ) (i : Fin (m + 1)) {p q : ℕ} (s : ShufflePath p q)
    (x : (simplicial (m + 1)) _⦋p⦌) (y : (simplicial n) _⦋q⦌) :
    (simplicial (m + n)) _⦋p + q⦌ :=
  (simplexEquiv (m + n) (p + q)).symm (fun k =>
    permutationComposition m n i (simplexEquiv (m + 1) p x (s.horizontal k))
      (simplexEquiv n q y (s.vertical k)))

/-- 概要：shuffle 単体の頂点は経路に沿う置換の部分合成である（Berger–Fresse §1.1.3）。
方針：単体と置換列の同値の往復を消去する。
規約：頂点 k は格子経路の二座標で指定される。
使われ方：退化性と等変性を頂点ごとに計算する。 -/
@[simp] lemma simplexEquiv_shuffleSimplex (m n : ℕ) (i : Fin (m + 1)) {p q : ℕ}
    (s : ShufflePath p q) (x : (simplicial (m + 1)) _⦋p⦌)
    (y : (simplicial n) _⦋q⦌) (k : Fin (p + q + 1)) :
    simplexEquiv (m + n) (p + q) (shuffleSimplex m n i s x y) k =
      permutationComposition m n i (simplexEquiv (m + 1) p x (s.horizontal k))
        (simplexEquiv n q y (s.vertical k)) := by
  simp only [shuffleSimplex, Equiv.apply_symm_apply]

variable (A : Type u) [CommRing A]

/-- 概要：二つの置換列の合成を全 shuffle 経路の符号つき和で定義する（Berger–Fresse §1.1.3）。
方針：各経路の合成単体を正規化し、shuffle 置換の signature を掛けて足す。
規約：入力が退化単体である場合もこの有限和自体は定義する。
使われ方：次数ごとの双線形合成を非退化生成元で指定する。 -/
def shuffleValue (m n : ℕ) (i : Fin (m + 1)) (p q : ℕ)
    (x : (simplicial (m + 1)) _⦋p⦌) (y : (simplicial n) _⦋q⦌) :
    (normalizedChains A (m + n)).X (p + q) :=
  ∑ s : ShufflePath p q, (s.sign : ℤ) •
    normalizedGenerator A (m + n) (p + q) (shuffleSimplex m n i s x y)

/-- 概要：shuffle の生成元の公式を正規化鎖上の双線形写像に延長する（Berger–Fresse §1.1.3）。
方針：二つの非退化単体基底に沿って順に線形延長する。
規約：p 次数と q 次数から p+q 次数への A 双線形写像である。
使われ方：微分との両立性を証明した後、複体上の部分合成へ束ねる。 -/
def shuffleBilinear (m n : ℕ) (i : Fin (m + 1)) (p q : ℕ) :
    (normalizedChains A (m + 1)).X p →ₗ[A]
      (normalizedChains A n).X q →ₗ[A] (normalizedChains A (m + n)).X (p + q) :=
  (normalizedBasis A (m + 1) p).constr A (fun x =>
    (normalizedBasis A n q).constr A (fun y => shuffleValue A m n i p q x.down.val y.down.val))

/-- 概要：双線形合成は非退化生成元で指定した shuffle 和に一致する（Berger–Fresse §1.1.3）。
方針：二つの基底について線形延長の生成元での値を計算する。
規約：両入力の非退化性を部分型で明示する。
使われ方：shuffle の鎖写像の条件とオペラッド法則を有限和の計算に帰着する。 -/
lemma shuffleBilinear_nondegenerate (m n : ℕ) (i : Fin (m + 1)) (p q : ℕ)
    (x : (simplicial (m + 1)).nonDegenerate p) (y : (simplicial n).nonDegenerate q) :
    shuffleBilinear A m n i p q (normalizedGenerator A (m + 1) p x.val)
      (normalizedGenerator A n q y.val) = shuffleValue A m n i p q x.val y.val := by
  rw [← normalizedBasis_apply A (m + 1) p x, ← normalizedBasis_apply A n q y]
  simp only [shuffleBilinear, Module.Basis.constr_basis]

end SerrePositivity.EInfinity.BarrattEccles
