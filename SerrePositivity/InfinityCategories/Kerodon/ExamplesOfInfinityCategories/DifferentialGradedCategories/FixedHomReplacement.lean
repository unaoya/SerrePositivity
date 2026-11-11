module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Replace
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomHEqAlgebra

/-! # 固定した端点の一射による成分置換

概要：部分集合の最小・最大頂点を端点とする一射から、全ての端点・次数指定に使える置換族を作る。
方針：端点と次数の等式による線形移送を使い、一集合の置換へ渡す。
規約：HA Proposition 1.3.1.10。使われ方：Hom-fiber で解いた成分を単体データへ組み込む。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：有効な固定端点と次数の一射を、その集合の任意の端点・次数指定の射族へ拡張する。
方針：同じ最小元・最大元・濃度から得られる三つの等式に沿って移送する。
規約：HA Construction 1.3.1.6。使われ方：未知成分を replace の入力形式へ変換する。 -/
def fixedHomFamily {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (M : Finset (Fin (n + 1))) (a₀ b₀ : Fin (n + 1)) (k₀ : ℤ)
    (hM : 2 ≤ M.card) (ha₀ : a₀ = M.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM))
    (hb₀ : b₀ = M.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM)) (hk₀ : k₀ = 2 - (M.card : ℤ))
    (f : GradedHom A (s.obj a₀) (s.obj b₀) k₀) :
    ∀ a b k (hI : 2 ≤ M.card),
      a = M.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI) → b = M.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI) →
      k = 2 - (M.card : ℤ) → GradedHom A (s.obj a) (s.obj b) k :=
  fun _ _ _ _ ha hb hk => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport (A := A) (D := D)
    (congrArg s.obj (ha₀.trans ha.symm)) (congrArg s.obj (hb₀.trans hb.symm))
    (hk₀.trans hk.symm) f

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (fixedHomFamily)


/-- 概要：固定端点・次数で射族を評価すると元の射に戻る。
方針：反射的な移送を評価し、証明の一意性を使う。
規約：HA Construction 1.3.1.6。使われ方：置換後の未知成分の値の計算。 -/
lemma fixedHomFamily_self {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (M : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (hM : 2 ≤ M.card) (ha : a = M.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM))
    (hb : b = M.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM)) (hk : k = 2 - (M.card : ℤ))
    (f : GradedHom A (s.obj a) (s.obj b) k) :
    s.fixedHomFamily M a b k hM ha hb hk f a b k hM ha hb hk = f := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (fixedHomFamily_self)


/-- 概要：一射から作った置換族の各値は元の射と異種等号で一致する。
方針：端点と次数による移送の異種等号を使う。
規約：HA Construction 1.3.1.6。使われ方：型付き解と単体データの成分を比較する。 -/
lemma fixedHomFamily_heq {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (M : Finset (Fin (n + 1))) (a₀ b₀ : Fin (n + 1)) (k₀ : ℤ)
    (hM : 2 ≤ M.card) (ha₀ : a₀ = M.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM))
    (hb₀ : b₀ = M.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM)) (hk₀ : k₀ = 2 - (M.card : ℤ))
    (f : GradedHom A (s.obj a₀) (s.obj b₀) k₀)
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ M.card)
    (ha : a = M.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = M.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (M.card : ℤ)) :
    HEq (s.fixedHomFamily M a₀ b₀ k₀ hM ha₀ hb₀ hk₀ f a b k hI ha hb hk) f :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_heq (A := A) (D := D) _ _ _ _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (fixedHomFamily_heq)


/-- 概要：有効な端点と次数の一射だけを指定して一集合の成分を置き換える。
方針：固定一射から作った射族を既存の replace へ渡す。
規約：HA Proposition 1.3.1.10。使われ方：標準 fiber 境界の先頭成分と D 成分の挿入。 -/
def replaceFixed {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (M : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (hM : 2 ≤ M.card) (ha : a = M.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM))
    (hb : b = M.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM)) (hk : k = 2 - (M.card : ℤ))
    (f : GradedHom A (s.obj a) (s.obj b) k) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n :=
  s.replace M (s.fixedHomFamily M a b k hM ha hb hk f)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (replaceFixed)


/-- 概要：固定一射による置換は、その一射を指定した端点と次数で回収する。
方針：置換の自己評価と射族の自己評価を順に使う。
規約：HA Proposition 1.3.1.10。使われ方：未知成分の微分方程式の左辺の同定。 -/
lemma replaceFixed_hom_same {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (M : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (hM : 2 ≤ M.card) (ha : a = M.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM))
    (hb : b = M.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM)) (hk : k = 2 - (M.card : ℤ))
    (f : GradedHom A (s.obj a) (s.obj b) k) :
    (s.replaceFixed M a b k hM ha hb hk f).hom M a b k hM ha hb hk = f := by
  unfold replaceFixed
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replace_hom_same, fixedHomFamily_self]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (replaceFixed_hom_same)


/-- 概要：固定一射の置換は別の集合の成分を変えない。
方針：固定一射を置換族に変換し、既存の置換の相違公式を使う。
規約：HA Proposition 1.3.1.10。使われ方：先頭と D 側の二成分を独立に挿入する。 -/
lemma replaceFixed_hom_of_ne {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (M : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (hM : 2 ≤ M.card) (ha : a = M.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM))
    (hb : b = M.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM)) (hk : k = 2 - (M.card : ℤ))
    (f : GradedHom A (s.obj a) (s.obj b) k)
    (I : Finset (Fin (n + 1))) (c d : Fin (n + 1)) (l : ℤ)
    (hI : 2 ≤ I.card) (hc : c = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hd : d = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hl : l = 2 - (I.card : ℤ)) (hne : I ≠ M) :
    (s.replaceFixed M a b k hM ha hb hk f).hom I c d l hI hc hd hl =
      s.hom I c d l hI hc hd hl := by
  unfold replaceFixed
  exact s.replace_hom_of_ne M _ I c d l hI hc hd hl hne

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (replaceFixed_hom_of_ne)


/-- 概要：固定一射で自分の集合を置換しても、その集合の右辺は変わらない。
方針：右辺は真部分集合の成分だけで決まるという既存の公式を使う。
規約：HA Proposition 1.3.1.10。使われ方：先頭成分の微分方程式を直接挿入する。 -/
lemma replaceFixed_rhs_self {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (M : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (hM : 2 ≤ M.card) (ha : a = M.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM))
    (hb : b = M.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM)) (hk : k = 2 - (M.card : ℤ))
    (f : GradedHom A (s.obj a) (s.obj b) k) :
    (s.replaceFixed M a b k hM ha hb hk f).rhs M a b k hM ha hb hk =
      s.rhs M a b k hM ha hb hk := by
  unfold replaceFixed
  exact s.rhs_replace_self M _ a b k hM ha hb hk

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (replaceFixed_rhs_self)


end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
