module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.TensorVectors

/-!
模型。文献の定義との比較は後で
# 任意の指定整数次数でのテンソル生成元

概要：Berger–Fresse §2.2.7 の境界で必要な整数次数の移送を整理する。
方針：元の斉次テンソル生成元を等式の射で移し、テンソル包含との両立を証明する。
規約：次数等式は常に証明を要求し、異なる次数の元を無条件に同一視しない。
使われ方：一因子を辺から端点へ置換した実際のテンソルを同じ境界成分へ置く。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable (A : Type u) [CommRing A]

/-- 概要：指定した整数次数で評価する反復テンソル生成元（BF §2.2.6–7）。
方針：総鎖次数の負と指定次数の等式の射を適用する。
規約：正しい次数である証明が必要。
使われ方：端点への置換後のテンソルと境界項の次数を一致させる。 -/
def tensorVectorAt (n : ℕ) (f : Fin n → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) (r : ℤ)
    (h : -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n f : ℤ) = r) : (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n).X r :=
  eqToHom (congrArg (fun s => (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n).X s) h) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVector A n f)

/-- 概要：元の総次数なら整数次数の移送は恒等（BF §2.2.6）。
方針：反射的な等式の射を消す。
規約：任意の出力族。
使われ方：次数移送の比較の基礎。 -/
@[simp] lemma tensorVectorAt_refl (n : ℕ) (f : Fin n → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt A n f (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n f : ℤ)) rfl = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVector A n f := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt, eqToHom_refl, ModuleCat.id_apply]

/-- 概要：等しい出力族の指定次数のテンソル生成元は等しい（BF §2.2.6）。
方針：出力族の等式を消去し、次数証明の一意性を使う。
規約：両族が同じ指定整数次数を持つことを証明する。
使われ方：端点置換の出力族を削除語の出力族へ同定する。 -/
lemma tensorVectorAt_congr (n : ℕ) (f g : Fin n → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) (r : ℤ)
    (hf : -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n f : ℤ) = r) (hg : -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n g : ℤ) = r) (hfg : f = g) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt A n f r hf = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt A n g r hg := by
  subst g
  rfl

/-- 概要：負自然数次数での評価は既存の指定鎖次数の評価と一致（BF §2.2.6）。
方針：二つの次数移送の定義を比較する。
規約：次数証明から同じ整数次数の証明を得る。
使われ方：整数次数の比較を切断成分の指定鎖次数へ戻す。 -/
lemma tensorVectorAt_natDegree (n q : ℕ) (f : Fin n → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n f = q) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt A n f (-(q : ℤ)) (congrArg (fun k : ℕ => -(k : ℤ)) h) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorOfDegree A n q f h := rfl

/-- 概要：斉次テンソル包含は三つの次数の等式による移送と両立（BF §2.2.7）。
方針：入力二次数と出力次数の等式を消去する。
規約：同じ全次数の各包含で用いる証明の違いは無視する。
使われ方：端点への置換の右括弧再帰式の次数を揃える。 -/
lemma tensorInclusion_transport (P Q : Complex A) (r s t r' s' t' : ℤ)
    (h : r + s = t) (h' : r' + s' = t') (hr : r = r') (hs : s = s') (ht : t = t')
    (x : P.X r) (y : Q.X s) :
    eqToHom (congrArg (fun k => (P ⊗ Q).X k) ht)
        (ιTensorObj P Q r s t h (x ⊗ₜ[A] y)) =
      ιTensorObj P Q r' s' t' h'
        (eqToHom (congrArg P.X hr) x ⊗ₜ[A] eqToHom (congrArg Q.X hs) y) := by
  subst r'
  subst s'
  subst t'
  simp only [eqToHom_refl, ModuleCat.id_apply]

/-- 概要：指定整数次数のテンソル生成元の再帰式（BF §2.2.6–7）。
方針：元の生成元の再帰式にテンソル包含の次数移送を適用する。
規約：先頭・後続・全体の次数をそれぞれ指定する。
使われ方：一因子置換の再帰式と境界項の再帰式を同じ型で比較する。 -/
lemma tensorVectorAt_succ (n : ℕ) (f : Fin (n + 1) → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) (r s t : ℤ)
    (hr : -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree (f 0) : ℤ) = r)
    (hs : -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n (fun i => f i.succ) : ℤ) = s) (ht : r + s = t) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt A (n + 1) f t (by
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree, Nat.cast_add]; omega) =
      ιTensorObj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n) r s t ht
        (eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).X hr) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A (f 0)) ⊗ₜ[A]
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt A n (fun i => f i.succ) s hs) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVector]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorInclusion_transport A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n) _ _ _ r s t _ ht hr hs
    (by simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree, Nat.cast_add]; omega) _ _

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
