module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.FirstBlockArities
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyHeadSeparation

/-!
模型。文献の定義との比較は後で
# 先頭ブロックをまとめた arity 族への再結合

概要：Berger–Moerdijk §1 の二段の全合成で、まとめた先頭演算を任意の arity ごとの複体族へ組み込む。
方針：先頭と後半の arity の等式で入力を移送し、一般の先頭の組み込み射を適用する。
規約：等式は複体のテンソル全体の移送に使い、追加の仮定を課さない。
使われ方：オペラッド係数、入力テンソル冪、両者の対で同じ組み込みを使う。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded
open scoped _root_.BigOperators

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：等しい先頭 arity と後半の族を使って先頭演算を組み込む（Berger–Moerdijk §1）。
方針：入力テンソルの等式で移送し、先頭の組み込み射を適用する。
規約：hq と ht は指定した入力族の表示の等式である。
使われ方：先頭ブロックの和で添字付けた演算を外側の族へ渡す。 -/
def arityHeadAssembly (D : ℕ → Complex A) (m : ℕ) (s : Fin (1 + m) → ℕ)
    (q : ℕ) (t : Fin m → ℕ) (hq : q = s ((0 : Fin 1).castAdd m))
    (ht : t = fun j => s (j.natAdd 1)) :
    D q ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily m (fun j => D (t j)) ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (1 + m) (fun j => D (s j)) :=
  eqToHom (by rw [hq, ht] : D q ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily m (fun j => D (t j)) =
    D (s ((0 : Fin 1).castAdd m)) ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily m (fun j => D (s (j.natAdd 1)))) ≫
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyHeadAssembly m (fun j => D (s j))

/-- 概要：arity の表示を移送した先頭の組み込みは族の射について自然（Berger–Moerdijk §1）。
方針：表示の等式を消去し、一般の先頭の組み込みの自然性を適用する。
規約：arity ごとの複体族とその射は任意。
使われ方：組み込んだ演算の生成射を入力ごとの生成射へ比較する。 -/
lemma arityHeadAssembly_naturality {D E : ℕ → Complex A} (f : ∀ r, D r ⟶ E r)
    (m : ℕ) (s : Fin (1 + m) → ℕ) (q : ℕ) (t : Fin m → ℕ)
    (hq : q = s ((0 : Fin 1).castAdd m)) (ht : t = fun j => s (j.natAdd 1)) :
    (f q ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap m (fun j => f (t j))) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.arityHeadAssembly E m s q t hq ht =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.arityHeadAssembly D m s q t hq ht ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap (1 + m) (fun j => f (s j)) := by
  subst q
  subst t
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.arityHeadAssembly, eqToHom_refl, Category.id_comp] using
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyHeadAssembly_naturality m (fun j => f (s j))

/-- 概要：移送した先頭の組み込みは係数列と入力列へ独立に分かれる（Berger–Moerdijk §1）。
方針：表示の等式を消去して先頭の組み込みとテンソル分離の両立を使う。
規約：D と E は独立な arity ごとの複体族。
使われ方：先頭の合成結果を係数側と入力側で独立に計算する。 -/
lemma arityHeadAssembly_tensor (D E : ℕ → Complex A)
    (m : ℕ) (s : Fin (1 + m) → ℕ) (q : ℕ) (t : Fin m → ℕ)
    (hq : q = s ((0 : Fin 1).castAdd m)) (ht : t = fun j => s (j.natAdd 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.arityHeadAssembly (fun r => D r ⊗ E r) m s q t hq ht ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso (1 + m) (fun j => D (s j)) (fun j => E (s j))).hom =
    ((D q ⊗ E q) ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso m (fun j => D (t j)) (fun j => E (t j))).hom) ≫
      tensorμ (D q) (E q) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily m (fun j => D (t j))) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily m (fun j => E (t j))) ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.arityHeadAssembly D m s q t hq ht ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.arityHeadAssembly E m s q t hq ht) := by
  subst q
  subst t
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.arityHeadAssembly, eqToHom_refl, Category.id_comp] using
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyHeadAssembly_tensor m (fun j => D (s j)) (fun j => E (s j))

/-- 概要：先頭ブロックを一演算へまとめた複体族を外側の入力へ組み込む（Berger–Moerdijk §1）。
方針：先頭ブロックの総 arity と後半の族を、まとめた arity 族へ移送する。
規約：空の前半と後半を許す。
使われ方：二段の全合成で係数と入力の両方を組み込む。 -/
def firstBlockFamilyAssembly (D : ℕ → Complex A) (n m : ℕ) (s : Fin (n + m) → ℕ) :
    D (∑ j : Fin n, s (j.castAdd m)) ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily m (fun j => D (s (j.natAdd n))) ⟶
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (1 + m) (fun j => D (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities n m s j)) :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.arityHeadAssembly D m (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities n m s) (∑ j : Fin n, s (j.castAdd m))
    (fun j => s (j.natAdd n)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities_head n m s).symm
    (funext fun j => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities_tail n m s j).symm)

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
