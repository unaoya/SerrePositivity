module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-!
概要：全射な可算加群逆系に対する差分射の全射性。
方針：各段階で原像を選んで差分方程式を再帰的に解く。
規約：係数環の可換性・平坦性は不要。
使われ方：TT §3、Toën §3.2、Stacks 15.88.12・36.3.4 の Milnor 列。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {H : Type u} [Ring H] (X : ℕ → ModuleCat.{u} H)
  (s : ∀ n, X (n + 1) ⟶ X n)

/--
概要：可算加群逆系の積の差分線形写像。
方針：第 n 成分を x_n − s_n x_{n+1} とする。
規約：具体的な従属関数の加群上で定義する。
使われ方：TT §3、Stacks 15.88 の逆極限の計算。
-/
def moduleSequenceDifference : (∀ n, X n) →ₗ[H] ∀ n, X n where
  toFun x n := x n - s n (x (n + 1))
  map_add' x y := by ext n; simp; abel
  map_smul' a x := by ext n; simp [smul_sub]

/--
概要：全射な遷移射を持つ逆系の差分方程式を解く。
方針：x_0=0 から始め、s_n x_{n+1}=x_n−y_n の原像を選ぶ。
規約：存在を仮定するフィールドを導入せず再帰的に構成する。
使われ方：TT §3、Stacks 15.88.12 の lim¹ 消滅。
-/
def moduleDifferenceSolution (hs : ∀ n, Function.Surjective (s n)) (y : ∀ n, X n) :
    ∀ n, X n
  | 0 => 0
  | n + 1 => Classical.choose (hs n (moduleDifferenceSolution hs y n - y n))

/--
概要：構成した列は実際に差分方程式を満たす。
方針：各段階の原像の選択の等式を使う。
規約：任意の右辺を許す。
使われ方：TT §3、Stacks 36.3.4 の Milnor 列の左端の消滅。
-/
lemma moduleSequenceDifference_solution (hs : ∀ n, Function.Surjective (s n))
    (y : ∀ n, X n) :
    moduleSequenceDifference X s (moduleDifferenceSolution X s hs y) = y := by
  ext n
  have h := Classical.choose_spec (hs n (moduleDifferenceSolution X s hs y n - y n))
  change moduleDifferenceSolution X s hs y n - s n
    (Classical.choose (hs n (moduleDifferenceSolution X s hs y n - y n))) = y n
  rw [h]
  abel

/--
概要：全射な遷移射を持つ加群逆系の差分射は全射。
方針：構成した解を各右辺の原像とする。
規約：係数環は任意の単位的環。
使われ方：TT §3、Toën §3.2、Stacks 36.3.4 の Milnor 列。
-/
lemma moduleSequenceDifference_surjective (hs : ∀ n, Function.Surjective (s n)) :
    Function.Surjective (moduleSequenceDifference X s) :=
  fun y => ⟨moduleDifferenceSolution X s hs y, moduleSequenceDifference_solution X s hs y⟩

end SerrePositivity.KST.DerivedGeometry
