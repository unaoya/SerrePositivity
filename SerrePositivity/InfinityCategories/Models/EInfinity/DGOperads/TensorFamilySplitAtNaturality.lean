module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilySplitAt
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilySplitNaturality

/-!
模型。文献の定義との比較は後で
# 二部分への有限テンソル分離の自然性

概要：Berger–Moerdijk §1 の部分合成則に必要な入力のブロック分離を射族と両立させる。
方針：後半の長さで帰納し、末尾分離、結合子、尾の再結合の自然性を使う。
規約：前半と後半の入力の射は独立でよい。
使われ方：Schur 入力の生成射とブロック分解を接続する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：末尾分離の逆射は各入力の射と両立する（Berger–Moerdijk §1）。
方針：分離の自然性に前後の逆射を合成して相殺する。
規約：末尾の因子と残りの族を独立に動かす。
使われ方：後半の最後の因子を再結合するときの射の比較に使う。 -/
lemma tensorFamilySplitLast_inv_naturality (n : ℕ) {V W : Fin (n + 1) → Complex A}
    (f : ∀ i, V i ⟶ W i) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun i => f i.castSucc) ⊗ₘ f (Fin.last n)) ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n W).inv =
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n V).inv ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap (n + 1) f := by
  have h := congrArg (fun z => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n V).inv ≫ z ≫
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n W).inv) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast_naturality n f)
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc] using h.symm

/-- 概要：二部分への分離同型は有限族の各入力の射について自然である（Berger–Moerdijk §1）。
方針：末尾分離の自然性に前半の帰納仮定を使い、結合子と尾の再結合へ射を通す。
規約：前半 n 個、後半 m 個の射のテンソルを出力に適用する。
使われ方：有限入力族のブロック分離を生成射と作用射へ適用する。 -/
lemma tensorFamilySplitAt_naturality (n m : ℕ) {V W : Fin (n + m) → Complex A}
    (f : ∀ i, V i ⟶ W i) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap (n + m) f ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitAt n m W).hom =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitAt n m V).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun i => f (i.castAdd m)) ⊗ₘ
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap m (fun i => f (i.natAdd n))) := by
  induction m with
  | zero =>
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitAt, Iso.symm_hom, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap, tensorHom_id]
    exact rightUnitor_inv_naturality _
  | succ m ih =>
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitAt, Iso.trans_hom, whiskerRightIso_hom,
      whiskerLeftIso_hom, Iso.symm_hom, Category.assoc]
    erw [reassoc_of% (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast_naturality (n + m) f)]
    rw [tensorHom_comp_whiskerRight_assoc, ih (fun i => f i.castSucc)]
    rw [← whiskerRight_comp_tensorHom_assoc]
    rw [associator_naturality_assoc]
    erw [tensorHom_comp_whiskerLeft]
    erw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast_inv_naturality m (fun i => f (i.natAdd n))]
    rw [← whiskerLeft_comp_tensorHom]
    rfl

/-- 概要：二部分の再結合は各入力の射と両立する（Berger–Moerdijk §1）。
方針：分離の自然性に前後の逆射を合成して相殺する。
規約：前半と後半の射のテンソルを再結合の前に適用する。
使われ方：入力のブロック分離から元のテンソル族へ戻す計算に使う。 -/
lemma tensorFamilySplitAt_inv_naturality (n m : ℕ) {V W : Fin (n + m) → Complex A}
    (f : ∀ i, V i ⟶ W i) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun i => f (i.castAdd m)) ⊗ₘ
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap m (fun i => f (i.natAdd n))) ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitAt n m W).inv =
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitAt n m V).inv ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap (n + m) f := by
  have h := congrArg (fun z => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitAt n m V).inv ≫ z ≫
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitAt n m W).inv) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitAt_naturality n m f)
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc] using h.symm

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
