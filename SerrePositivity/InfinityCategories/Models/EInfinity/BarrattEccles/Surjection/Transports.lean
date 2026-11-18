module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Modules

/-!
模型。文献の定義との比較は後で
# 全射語加群の arity と次数の等式移送

概要：Berger–Fresse §1.2 の微分・単位・結合則で現れる添字の等式を扱う。
方針：加群への等式の射を線形写像として使う。
規約：基底の選択や符号の変更は行わない。
使われ方：TR の全射性から χ のオペラッド法則を移す。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.CategoryTheory

/-- 概要：次数の等式による全射語加群の線形移送（BF §1.2.3）。
方針：次数を加群へ送った等式の射を取る。
規約：次数を変えても文字の値を変えない。
使われ方：Leibniz 則と結合則の出力次数の括弧を揃える。 -/
def degreeTransport (A : Type u) [CommRing A] (n : ℕ) {p q : ℕ} (h : p = q) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A n p →ₗ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A n q :=
  (eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A n) h)).hom

/-- 概要：次数の恒等移送は元を変えない（BF §1.2.3）。
方針：等式の射を評価する。
規約：等式の証明には依存しない。
使われ方：同じ次数の移送を簡約する。 -/
@[simp] lemma degreeTransport_refl (A : Type u) [CommRing A] (n d : ℕ)
    (x : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A n d) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeTransport A n rfl x = x := rfl

/-- 概要：arity の等式による全射語加群の線形移送（BF §1.2.4）。
方針：arity を加群へ送った等式の射を取る。
規約：arity の等式以外に同値を選択しない。
使われ方：単位則と結合則の出力 arity の括弧を揃える。 -/
def arityTransport (A : Type u) [CommRing A] {m n : ℕ} (h : m = n) (d : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A m d →ₗ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A n d :=
  (eqToHom (congrArg (fun n => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A n d) h)).hom

/-- 概要：arity の恒等移送は元を変えない（BF §1.2.4）。
方針：等式の射を評価する。
規約：次数は固定する。
使われ方：同じ arity の移送を簡約する。 -/
@[simp] lemma arityTransport_refl (A : Type u) [CommRing A] (n d : ℕ)
    (x : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A n d) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.arityTransport A rfl d x = x := rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
