module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamily

/-!
模型。文献の定義との比較は後で
# 有限テンソル族の最後の因子の分離の自然性

概要：Berger–Moerdijk §1 の全入力への代入で最後の内側演算を分離する同型の自然性を示す。
方針：有限族の長さで帰納し、単位子と結合子の自然性を使う。
規約：射族は任意で、各入力の複体は独立に変えてよい。
使われ方：部分合成の等変性を全入力への合成の等変性へ帰納的に拡張する。
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

/-- 概要：最後の因子を分離する同型は全入力の射族について自然である（Berger–Moerdijk §1）。
方針：先頭の射と残りの族に分け、帰納仮定と結合子の自然性を適用する。
規約：前半の族は `Fin.castSucc`、最後の因子は `Fin.last` で指定する。
使われ方：全入力への代入の再帰で、各入力の置換を最後の入力と残りの族へ分ける。 -/
lemma tensorFamilySplitLast_naturality (n : ℕ) {V W : Fin (n + 1) → Complex A}
    (f : ∀ i, V i ⟶ W i) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap (n + 1) f ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n W).hom =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n V).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun i => f i.castSucc) ⊗ₘ f (Fin.last n)) := by
  induction n with
  | zero =>
    change (f 0 ⊗ₘ 𝟙 (𝟙_ (Complex A))) ≫ (ρ_ (W 0)).hom ≫ (λ_ (W 0)).inv =
      ((ρ_ (V 0)).hom ≫ (λ_ (V 0)).inv) ≫ (𝟙 (𝟙_ (Complex A)) ⊗ₘ f 0)
    rw [tensorHom_id, rightUnitor_naturality_assoc, leftUnitor_inv_naturality,
      id_tensorHom, Category.assoc]
  | succ n ih =>
    have ht :
        (f 0 ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap (n + 1) (fun i => f i.succ)) ≫
          (W 0 ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n (fun i => W i.succ)).hom) =
        (V 0 ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n (fun i => V i.succ)).hom) ≫
          (f 0 ⊗ₘ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun i => f i.castSucc.succ) ⊗ₘ f (Fin.last (n + 1)))) := by
      simp only [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
      rw [ih]
      rfl
    change (f 0 ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap (n + 1) (fun i => f i.succ)) ≫ _ = _
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast, Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom,
      Category.assoc]
    rw [← Category.assoc, ht, Category.assoc,
      associator_inv_naturality]
    rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
