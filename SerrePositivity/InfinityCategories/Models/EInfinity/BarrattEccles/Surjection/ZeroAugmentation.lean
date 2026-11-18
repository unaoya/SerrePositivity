module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Modules
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.ListGenerators

/-!
模型。文献の定義との比較は後で
# χ の零次の係数 augmentation

概要：Berger–Fresse §1.2・§3.1 の次数零演算が頂点に与える係数をまとめる。
方針：全ての非退化全射語基底を一へ送る線形写像を構成する。
規約：これは零次加群の写像であり、オペラッド augmentation を仮定しない。
使われ方：TR と BE augmentation の零次比較、区間の端点・収縮の余作用保存。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

variable (A : Type u) [CommRing A]

/-- 概要：χ の零次の各基底係数を足す線形写像（BF §1.2・§3.1）。
方針：自由語基底の全ての像を一として延長する。
規約：nullary の唯一の空語基底も一へ送る。
使われ方：区間頂点での一定出力テンソルのスカラー係数。 -/
def zeroAugmentation (n : ℕ) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A n 0 →ₗ[A] A :=
  (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n 0).constr A (fun _ => 1)

/-- 概要：零次の各 χ 基底の augmentation 値は一（BF §1.2・§3.1）。
方針：自由基底による線形延長を評価する。
規約：全 arity。
使われ方：TR の零次生成元との比較。 -/
@[simp] lemma zeroAugmentation_basis {n : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n 0) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.zeroAugmentation A n (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n 0 (ULift.up v)) = 1 :=
  Module.Basis.constr_basis (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n 0) A _ _

/-- 概要：零次の全射語の生成元の augmentation 値は一（BF §1.2・§3.1）。
方針：等濃度の全射は単射なので非退化基底として評価する。
規約：零 arity を含む。
使われ方：一行の table reduction と空語の係数を計算する。 -/
lemma zeroAugmentation_generator {n : ℕ} (v : Fin n → Fin n) (hv : Function.Surjective v) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.zeroAugmentation A n (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator A (d := 0) v) = 1 := by
  let w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n 0 :=
    ⟨v, hv, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.nondegenerate_of_injective (Finite.injective_iff_surjective.mpr hv)⟩
  rw [show _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator A (d := 0) v = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n 0 (ULift.up w) from _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator_word A w,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.zeroAugmentation_basis]

/-- 概要：空リストの零次 augmentation 値は一（BF §0・§1.2）。
方針：唯一の空の有限関数のリスト表示と生成元公式を使う。
規約：arity 零・次数零。
使われ方：nullary の table reduction の係数比較。 -/
lemma zeroAugmentation_empty :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.zeroAugmentation A 0 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listGenerator A (n := 0) (d := 0) []) = 1 := by
  have he : List.ofFn (fun i : Fin 0 => Fin.elim0 i : Fin 0 → Fin 0) = [] := by simp
  rw [← he, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listGenerator_ofFn]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.zeroAugmentation_generator A _ (fun a => Fin.elim0 a)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
