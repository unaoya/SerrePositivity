module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorSeparationBraiding
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorSwapNaturality

/-!
模型。文献の定義との比較は後で
# テンソル分離と三因子の先頭交換

概要：Berger–Moerdijk §1 の Schur 作用で先頭二入力の交換を係数と入力へ分離する。
方針：結合子、二つの対の交換、tensorμ の自然性を順に適用する。
規約：最後の対は固定し、各対の二列は独立の複体とする。
使われ方：有限テンソル族の分離同型と隣接交換の両立の基底となる。
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

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：三つのテンソル対の先頭交換は分離後の二列の先頭交換になる（Berger–Moerdijk §1）。
方針：交換後の結合則を展開し、二対の交換を分離し、自然性で最後の対へ運ぶ。
規約：最後の二対象 R,S は固定する。
使われ方：有限族の先頭交換と係数・入力の分離の可換性を証明する。 -/
lemma tensorTripleSwapIso_separation (V W V' W' R S : Complex A) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorTripleSwapIso (V ⊗ W) (V' ⊗ W') (R ⊗ S)).hom ≫
      ((V' ⊗ W') ◁ tensorμ V W R S) ≫ tensorμ V' W' (V ⊗ R) (W ⊗ S) =
    ((V ⊗ W) ◁ tensorμ V' W' R S) ≫ tensorμ V W (V' ⊗ R) (W' ⊗ S) ≫
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorTripleSwapIso V V' R).hom ⊗ₘ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorTripleSwapIso W W' S).hom) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorTripleSwapIso, Iso.trans_hom, Iso.symm_hom,
    whiskerRightIso_hom, Category.assoc]
  rw [← tensor_associativity V' W' V W R S]
  rw [← comp_whiskerRight_assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorμ_braiding, comp_whiskerRight_assoc]
  rw [tensorμ_natural_left_assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorμ_associativity_inv_assoc V W V' W' R S]
  simp only [← tensorHom_comp_tensorHom]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
