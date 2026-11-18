module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilySplitTwo
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyAdjacent
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.LastAdjacentSlots
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SplitPairCoherence

/-!
模型。文献の定義との比較は後で
# 末尾二因子の分離の再帰と交換後の対象

概要：Berger–Moerdijk §1 の末尾二入力の交換と末尾二因子の分離を比較するための再帰を証明する。
方針：二回の一因子の分離を結合子の自然性と pentagon でまとめる。
規約：末尾二因子の対を右括弧で保ち、前半の族は元の順序を保つ。
使われ方：末尾の隣接交換と二因子の分離の両立の帰納法に使う。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.Coxeter

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLastTwo

/-- 概要：二因子だけの族の末尾二因子の分離を単位子で表す（Berger–Moerdijk §1）。
方針：二回の分離を展開し、単位子と結合子の整合性を使う。
規約：前半は空の族でテンソル単位となる。
使われ方：末尾交換と分離の両立の帰納法の基底に使う。 -/
lemma tensorFamilySplitLastTwo_zero (V : Fin 2 → Complex A) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLastTwo 0 V).hom =
      (V 0 ◁ (ρ_ (V 1)).hom) ≫ (λ_ (V 0 ⊗ V 1)).inv := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLastTwo, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily,
    Iso.trans_hom, whiskerLeftIso_hom, whiskerRightIso_hom, Iso.symm_hom]
  monoidal

-- テンソル対象の比較で複体の余極限の実装へ展開するのを避ける。
-- モノイダル構造の射の整合性は SplitPairCoherence で既に証明している。
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：末尾二因子の分離は先頭を保って尾を分離する再帰に一致する（Berger–Moerdijk §1）。
方針：結合子の自然性と四因子の pentagon の比較で二回の分離を整理する。
規約：先頭の因子と末尾の二因子の対を最後に括り直す。
使われ方：末尾交換の比較を尾の族へ帰納する。 -/
lemma tensorFamilySplitLastTwo_succ (n : ℕ) (V : Fin (n + 3) → Complex A) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLastTwo (n + 1) V).hom =
      (V 0 ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLastTwo n (fun i => V i.succ)).hom) ≫
        (α_ (V 0) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => V i.castSucc.castSucc.succ))
          (V (Fin.last (n + 1)).castSucc ⊗ V (Fin.last (n + 2)))).inv := by
  have h := @_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.splitPairIso_whiskerLeft (Complex A) (inferInstance) (inferInstance) (V 0)
    (X := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + 2) (fun i => V i.succ))
    (Y := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + 1) (fun i => V i.castSucc.succ))
    (L := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => V i.castSucc.castSucc.succ))
    (U := V (Fin.last (n + 1)).castSucc) (V := V (Fin.last (n + 2)))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast (n + 1) (fun i => V i.succ))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n (fun i => V i.castSucc.succ))
  dsimp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLastTwo, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily,
    Fin.castSucc, Fin.succ, Fin.last, Fin.castAdd, Fin.castLE] at h ⊢
  simp only [Iso.trans_hom, whiskerLeftIso_hom, whiskerRightIso_hom,
    Iso.symm_hom, Category.assoc] at h ⊢
  exact h

/-- 概要：末尾交換後の分離の対象は前半と交換した二因子のテンソルである（Berger–Moerdijk §1）。
方針：最後の隣接互換の前半、最後から二番目、最後での値を計算する。
規約：前半の n 個の因子の順序は変えない。
使われ方：末尾交換後の分離の終域を元の前半と交換した二因子へ移す。 -/
lemma tensorFamily_lastSwap_output_obj (n : ℕ) (V : Fin (n + 2) → Complex A) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => V (adjacentTransposition (Fin.last n) i.castSucc.castSucc)) ⊗
        (V (adjacentTransposition (Fin.last n) (Fin.last n).castSucc) ⊗
          V (adjacentTransposition (Fin.last n) (Fin.last (n + 1)))) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => V i.castSucc.castSucc) ⊗
        (V (Fin.last (n + 1)) ⊗ V (Fin.last n).castSucc) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.adjacentLast_prefix, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.adjacentLast_penultimate, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.adjacentLast_last]

/-- 概要：等しい入力族の末尾二因子の分離は共通の始域と終域への移送後に一致する（Berger–Moerdijk §1）。
方針：入力族の等式で置き換え、等式の証明の一意性を使う。
規約：両方の分離を同じ二対象の間の射として比較する。
使われ方：末尾交換後の族を先頭と尾で記述した族へ置き換える。 -/
lemma tensorFamilySplitLastTwo_compare (n : ℕ) {V W : Fin (n + 2) → Complex A}
    (h : V = W) {S T : Complex A}
    (hs : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + 2) V = S) (ht : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + 2) W = S)
    (os : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => V i.castSucc.castSucc) ⊗
      (V (Fin.last n).castSucc ⊗ V (Fin.last (n + 1))) = T)
    (ot : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => W i.castSucc.castSucc) ⊗
      (W (Fin.last n).castSucc ⊗ W (Fin.last (n + 1))) = T) :
    eqToHom ht.symm ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLastTwo n W).hom ≫ eqToHom ot =
      eqToHom hs.symm ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLastTwo n V).hom ≫ eqToHom os := by
  subst W
  rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
