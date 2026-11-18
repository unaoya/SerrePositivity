module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurComposition

/-!
模型。文献の定義との比較は後で
# テンソル分離と交換

概要：Berger–Moerdijk §1 の自由代数の外側等変性で係数と入力の交換を分離する。
方針：対称モノイダル圏の tensorμ と braiding の両立を用いる。
規約：四つの対象は互いに異なってよい。
使われ方：有限族の隣接交換が係数と底の入力の独立な交換へ移ることを証明する。
-/

@[expose] public section

universe v u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- 概要：二つのテンソル対の交換は、係数と入力を分離するとそれぞれの交換となる（Berger–Moerdijk §1）。
方針：tensorμ を結合子と braiding で展開し、対称モノイダル圏の自然性と六角形の式を使う。
規約：交換前後で各対象の内部の射は恒等射。
使われ方：有限テンソル族の分離同型と先頭交換の両立の基底となる。 -/
lemma tensorμ_braiding (V W V' W' : C) :
    (β_ (V ⊗ W) (V' ⊗ W')).hom ≫ tensorμ V' W' V W =
      tensorμ V W V' W' ≫ ((β_ V V').hom ⊗ₘ (β_ W W').hom) := by
  simp [tensorμ, SymmetricCategory.braiding_swap_eq_inv_braiding W' V, tensorHom_def]

/-- 概要：三つのテンソル対の分離は結合子の逆射と両立する（Berger–Moerdijk §1）。
方針：tensor_associativity の前後の結合子を相殺する。
規約：分離後の二列はそれぞれ右括弧で表す。
使われ方：先頭二因子の交換の前後で分離の括弧を移す。 -/
@[reassoc]
lemma tensorμ_associativity_inv (V W V' W' R S : C) :
    (α_ (V ⊗ W) (V' ⊗ W') (R ⊗ S)).inv ≫
      (tensorμ V W V' W' ▷ (R ⊗ S)) ≫ tensorμ (V ⊗ V') (W ⊗ W') R S =
    ((V ⊗ W) ◁ tensorμ V' W' R S) ≫ tensorμ V W (V' ⊗ R) (W' ⊗ S) ≫
      ((α_ V V' R).inv ⊗ₘ (α_ W W' S).inv) := by
  apply (cancel_epi (α_ (V ⊗ W) (V' ⊗ W') (R ⊗ S)).hom).1
  simp only [Iso.hom_inv_id_assoc]
  apply (cancel_mono ((α_ V V' R).hom ⊗ₘ (α_ W W' S).hom)).1
  simp only [Category.assoc, tensorHom_comp_tensorHom, Iso.inv_hom_id,
    tensorHom_id, id_whiskerRight, Category.comp_id]
  exact tensor_associativity V W V' W' R S

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
