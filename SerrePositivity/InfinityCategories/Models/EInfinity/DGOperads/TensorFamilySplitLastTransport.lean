module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyAdjacent
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AdjacentCastSucc

/-!
模型。文献の定義との比較は後で
# 最後の因子の分離の再帰と入力族の移送

概要：Berger–Moerdijk §1 の末尾を固定する隣接交換と分離の比較に使う再帰と移送を整理する。
方針：分離の定義の一段を明示し、等しい入力族を共通の始域と終域で比較する。
規約：最後の因子を右側に分離する。
使われ方：任意の隣接位置の反復合成の外側等変性を帰納的に証明する。
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

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：最後の因子の分離は先頭を保つ尾の分離と逆結合子で計算できる（Berger–Moerdijk §1）。
方針：分離同型の再帰定義の射を評価する。
規約：前半の入力は castSucc で指定する。
使われ方：隣接交換と分離の比較を尾へ帰納する。 -/
lemma tensorFamilySplitLast_succ (n : ℕ) (V : Fin (n + 2) → Complex A) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast (n + 1) V).hom =
      (V 0 ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n (fun i => V i.succ)).hom) ≫
        (α_ (V 0) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => V i.castSucc.succ))
          (V (Fin.last (n + 1)))).inv := rfl

attribute [local irreducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast

/-- 概要：最後の因子の分離を先頭二因子と残りの族に分けて計算する（Berger–Moerdijk §1）。
方針：分離の一段の再帰式を二回適用し whisker の合成則で整理する。
規約：先頭は 0,1 の二位置で指定する。
使われ方：先頭二因子の交換と最後の分離の可換性を四因子の整合性へ帰着する。 -/
lemma tensorFamilySplitLast_two_head (n : ℕ) (V : Fin (n + 3) → Complex A) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast (n + 2) V).hom =
      (V 0 ◁ (V 1 ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n (fun i => V i.succ.succ)).hom)) ≫
        (V 0 ◁ (α_ (V 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => V i.castSucc.succ.succ))
          (V (Fin.last (n + 2)))).inv) ≫
        (α_ (V 0) (V 1 ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => V i.castSucc.succ.succ))
          (V (Fin.last (n + 2)))).inv := by
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast_succ (n + 1) V
  conv_rhs at h =>
    arg 1
    arg 2
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast_succ n (fun i => V i.succ)]
  simp only [whiskerLeft_comp, Fin.succ_zero_eq_one, Category.assoc] at h
  dsimp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily, Fin.last, Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ] at h ⊢
  exact h

/-- 概要：等しい入力族の最後の因子の分離は共通の始域と終域への移送後に一致する（Berger–Moerdijk §1）。
方針：入力族の等式で置き換え、等式の証明の一意性を使う。
規約：始域と終域の比較の等式をそれぞれ明示する。
使われ方：交換後の入力族を先頭と尾の具体的な記述へ置き換える。 -/
lemma tensorFamilySplitLast_compare (n : ℕ) {V W : Fin (n + 1) → Complex A}
    (h : V = W) {S T : Complex A}
    (hs : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + 1) V = S) (ht : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + 1) W = S)
    (os : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => V i.castSucc) ⊗ V (Fin.last n) = T)
    (ot : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => W i.castSucc) ⊗ W (Fin.last n) = T) :
    eqToHom ht.symm ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n W).hom ≫ eqToHom ot =
      eqToHom hs.symm ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n V).hom ≫ eqToHom os := by
  subst W
  rfl

/-- 概要：末尾を固定する隣接交換後の分離の終域は前半を交換した族と元の最後の因子になる（Berger–Moerdijk §1）。
方針：持ち上げた隣接互換の前半と最後での値を計算する。
規約：最後の因子は右側に固定する。
使われ方：前半の隣接交換と最後の分離の可換性の終域を同定する。 -/
lemma tensorFamily_adjacentCastSucc_output_obj (n : ℕ) (V : Fin (n + 2) → Complex A)
    (i : Fin n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + 1) (fun j => V (adjacentTransposition i.castSucc j.castSucc)) ⊗
        V (adjacentTransposition i.castSucc (Fin.last (n + 1))) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + 1) (fun j => V (adjacentTransposition i j).castSucc) ⊗
        V (Fin.last (n + 1)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.adjacentCastSucc_prefix, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.adjacentCastSucc_last]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
