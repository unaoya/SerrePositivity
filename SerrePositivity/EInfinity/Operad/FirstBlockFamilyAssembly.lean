module

public import SerrePositivity.EInfinity.Operad.FirstBlockArities
public import SerrePositivity.EInfinity.Operad.TensorFamilyHeadSeparation

/-!
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

namespace SerrePositivity.EInfinity

open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
open scoped BigOperators

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] tensorFamily
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：等しい先頭 arity と後半の族を使って先頭演算を組み込む（Berger–Moerdijk §1）。
方針：入力テンソルの等式で移送し、先頭の組み込み射を適用する。
規約：hq と ht は指定した入力族の表示の等式である。
使われ方：先頭ブロックの和で添字付けた演算を外側の族へ渡す。 -/
def arityHeadAssembly (D : ℕ → Complex A) (m : ℕ) (s : Fin (1 + m) → ℕ)
    (q : ℕ) (t : Fin m → ℕ) (hq : q = s ((0 : Fin 1).castAdd m))
    (ht : t = fun j => s (j.natAdd 1)) :
    D q ⊗ tensorFamily m (fun j => D (t j)) ⟶ tensorFamily (1 + m) (fun j => D (s j)) :=
  eqToHom (by rw [hq, ht] : D q ⊗ tensorFamily m (fun j => D (t j)) =
    D (s ((0 : Fin 1).castAdd m)) ⊗ tensorFamily m (fun j => D (s (j.natAdd 1)))) ≫
    tensorFamilyHeadAssembly m (fun j => D (s j))

/-- 概要：arity の表示を移送した先頭の組み込みは族の射について自然（Berger–Moerdijk §1）。
方針：表示の等式を消去し、一般の先頭の組み込みの自然性を適用する。
規約：arity ごとの複体族とその射は任意。
使われ方：組み込んだ演算の生成射を入力ごとの生成射へ比較する。 -/
lemma arityHeadAssembly_naturality {D E : ℕ → Complex A} (f : ∀ r, D r ⟶ E r)
    (m : ℕ) (s : Fin (1 + m) → ℕ) (q : ℕ) (t : Fin m → ℕ)
    (hq : q = s ((0 : Fin 1).castAdd m)) (ht : t = fun j => s (j.natAdd 1)) :
    (f q ⊗ₘ tensorFamilyMap m (fun j => f (t j))) ≫ arityHeadAssembly E m s q t hq ht =
      arityHeadAssembly D m s q t hq ht ≫ tensorFamilyMap (1 + m) (fun j => f (s j)) := by
  subst q
  subst t
  simpa only [arityHeadAssembly, eqToHom_refl, Category.id_comp] using
    tensorFamilyHeadAssembly_naturality m (fun j => f (s j))

/-- 概要：移送した先頭の組み込みは係数列と入力列へ独立に分かれる（Berger–Moerdijk §1）。
方針：表示の等式を消去して先頭の組み込みとテンソル分離の両立を使う。
規約：D と E は独立な arity ごとの複体族。
使われ方：先頭の合成結果を係数側と入力側で独立に計算する。 -/
lemma arityHeadAssembly_tensor (D E : ℕ → Complex A)
    (m : ℕ) (s : Fin (1 + m) → ℕ) (q : ℕ) (t : Fin m → ℕ)
    (hq : q = s ((0 : Fin 1).castAdd m)) (ht : t = fun j => s (j.natAdd 1)) :
    arityHeadAssembly (fun r => D r ⊗ E r) m s q t hq ht ≫
      (tensorFamilyTensorIso (1 + m) (fun j => D (s j)) (fun j => E (s j))).hom =
    ((D q ⊗ E q) ◁ (tensorFamilyTensorIso m (fun j => D (t j)) (fun j => E (t j))).hom) ≫
      tensorμ (D q) (E q) (tensorFamily m (fun j => D (t j))) (tensorFamily m (fun j => E (t j))) ≫
      (arityHeadAssembly D m s q t hq ht ⊗ₘ arityHeadAssembly E m s q t hq ht) := by
  subst q
  subst t
  simpa only [arityHeadAssembly, eqToHom_refl, Category.id_comp] using
    tensorFamilyHeadAssembly_tensor m (fun j => D (s j)) (fun j => E (s j))

/-- 概要：先頭ブロックを一演算へまとめた複体族を外側の入力へ組み込む（Berger–Moerdijk §1）。
方針：先頭ブロックの総 arity と後半の族を、まとめた arity 族へ移送する。
規約：空の前半と後半を許す。
使われ方：二段の全合成で係数と入力の両方を組み込む。 -/
def firstBlockFamilyAssembly (D : ℕ → Complex A) (n m : ℕ) (s : Fin (n + m) → ℕ) :
    D (∑ j : Fin n, s (j.castAdd m)) ⊗ tensorFamily m (fun j => D (s (j.natAdd n))) ⟶
      tensorFamily (1 + m) (fun j => D (firstBlockArities n m s j)) :=
  arityHeadAssembly D m (firstBlockArities n m s) (∑ j : Fin n, s (j.castAdd m))
    (fun j => s (j.natAdd n)) (firstBlockArities_head n m s).symm
    (funext fun j => (firstBlockArities_tail n m s j).symm)

end SerrePositivity.EInfinity
