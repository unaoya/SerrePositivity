module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurComposition

/-!
模型。文献の定義との比較は後で
# 係数と入力を分離する有限テンソル同型の自然性

概要：Berger–Moerdijk §1 の自由代数の合成で係数と入力を分ける同型の自然性を示す。
方針：有限族の長さで帰納し、Koszul 交換を含む `tensorμ` の自然性を適用する。
規約：係数側と入力側に独立な複体射を許す。arity 0 の族も含む。
使われ方：生成射の同時置換を係数の置換と連結入力の置換へ分離する。
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

/-- 概要：係数と入力を分離する同型は両者の射族について自然である（Berger–Moerdijk §1）。
方針：先頭の二因子の射と残りの族に分け、テンソル交換の自然性を使う。
規約：有限族の添字は固定し、四つの複体族の間の任意の射を扱う。
使われ方：Schur 合成の入力ごとの coinvariant 関係を検証する。 -/
lemma tensorFamilyTensorIso_naturality (n : ℕ) {V W V' W' : Fin n → Complex A}
    (f : ∀ i, V i ⟶ V' i) (g : ∀ i, W i ⟶ W' i) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun i => f i ⊗ₘ g i) ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso n V' W').hom =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso n V W).hom ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n f ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n g) := by
  induction n with
  | zero =>
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso, Iso.symm_hom,
      tensorHom_id, id_whiskerRight, Category.id_comp, Category.comp_id]
  | succ n ih =>
    have ht :
        ((f 0 ⊗ₘ g 0) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun i => f i.succ ⊗ₘ g i.succ)) ≫
          ((V' 0 ⊗ W' 0) ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso n
            (fun i => V' i.succ) (fun i => W' i.succ)).hom) =
        ((V 0 ⊗ W 0) ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso n
          (fun i => V i.succ) (fun i => W i.succ)).hom) ≫
          ((f 0 ⊗ₘ g 0) ⊗ₘ
            (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun i => f i.succ) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun i => g i.succ))) := by
      simp only [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
      rw [ih]
    change ((f 0 ⊗ₘ g 0) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun i => f i.succ ⊗ₘ g i.succ)) ≫ _ = _
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso, Iso.trans_hom, whiskerLeftIso_hom, Category.assoc]
    rw [← Category.assoc _ _ (tensorμ _ _ _ _), ht]
    rw [Category.assoc, tensorμ_natural]
    rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
