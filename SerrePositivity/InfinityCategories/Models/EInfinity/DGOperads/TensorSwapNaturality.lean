module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamily

/-!
模型。文献の定義との比較は後で
# 異なる二因子を交換するテンソル同型の自然性

概要：Berger–Moerdijk §1 の外側等変性に用いる、最初の二因子を交換する同型を構成する。
方針：結合子と Koszul 対称性を合成し、三つの因子の独立な射について自然性を証明する。
規約：三つの因子は互いに異なる複体でよい。
使われ方：有限テンソル族の隣接交換を入力の生成射と両立させる。
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

/-- 概要：三因子の右括弧テンソルの最初の二因子を交換する（Berger–Moerdijk §1）。
方針：最初の二因子を括り、Koszul 対称性を適用して括弧を戻す。
規約：最後の因子は固定する。
使われ方：有限テンソル族の先頭の隣接交換を構成する。 -/
def tensorTripleSwapIso (R S T : Complex A) : R ⊗ (S ⊗ T) ≅ S ⊗ (R ⊗ T) :=
  (α_ R S T).symm ≪≫ whiskerRightIso (β_ R S) T ≪≫ α_ S R T

/-- 概要：最初の二因子の交換は三つの因子の射について自然である（Berger–Moerdijk §1）。
方針：結合子の自然性と二因子の Koszul 対称性の自然性を組み合わせる。
規約：三つの因子の射は独立でよい。
使われ方：Schur 入力の生成射を隣接交換の前後で比較する。 -/
lemma tensorTripleSwapIso_naturality {R S T R' S' T' : Complex A}
    (f : R ⟶ R') (g : S ⟶ S') (h : T ⟶ T') :
    (f ⊗ₘ (g ⊗ₘ h)) ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorTripleSwapIso R' S' T').hom =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorTripleSwapIso R S T).hom ≫ (g ⊗ₘ (f ⊗ₘ h)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorTripleSwapIso, Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom,
    Category.assoc]
  rw [associator_inv_naturality_assoc]
  have hb : ((f ⊗ₘ g) ⊗ₘ h) ≫ ((β_ R' S').hom ▷ T') =
      ((β_ R S).hom ▷ T) ≫ ((g ⊗ₘ f) ⊗ₘ h) := by
    simp only [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
    exact congrArg (fun k => k ⊗ₘ h) (BraidedCategory.braiding_naturality f g)
  rw [← Category.assoc _ _ (α_ S' R' T').hom, hb, Category.assoc, associator_naturality]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
