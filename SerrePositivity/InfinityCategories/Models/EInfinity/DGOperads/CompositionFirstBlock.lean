module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionAheadBlockFactor
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionHeadFactor

/-!
模型。文献の定義との比較は後で
# 全合成の先頭ブロックをまとめる

概要：Berger–Moerdijk §1 の先頭での部分合成と全合成の両立を、先頭ブロックの合成で表す。
方針：内側の全合成をテンソル代入の前へ移し、外側の先頭分解の単位因子を相殺する。
規約：先頭ブロック内の入力順序と後半の入力順序を保つ。
使われ方：自由代数の部分合成則で係数の合成の二通りの順序を比較する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded
open scoped _root_.BigOperators

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：先頭への部分合成後の全合成は、先頭ブロックをまとめてから計算できる（Berger–Moerdijk §1）。
方針：平行則と入れ子則で得た式から、内側の全合成をテンソル代入の前へ移す。
規約：出力の arity は元の入力族 s の和へ移送する。
使われ方：外側の全合成の先頭分解と係数射を比較する。 -/
lemma composition_after_first_block (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (m n : ℕ) (s : Fin (n + m) → ℕ) :
    (P.composeAheadOfInputs m 0 n ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + m) (fun j => P.arity (s j))) ≫
      P.composition (n + m) s =
    ((P.arity (1 + m) ⊗ P.arity n) ◁
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitAt n m (fun j => P.arity (s j))).hom) ≫
    (α_ (P.arity (1 + m)) (P.arity n)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => P.arity (s (j.castAdd m))) ⊗
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily m (fun j => P.arity (s (j.natAdd n))))).hom ≫
      (P.arity (1 + m) ◁ (α_ (P.arity n)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => P.arity (s (j.castAdd m))))
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily m (fun j => P.arity (s (j.natAdd n))))).inv) ≫
      (P.arity (1 + m) ◁ (P.composition n (fun j => s (j.castAdd m)) ▷
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily m (fun j => P.arity (s (j.natAdd n))))) ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep (P.composeAfterInputsFlat 1 m 0 (fun j => s (j.natAdd n)))
        (P.composeAheadOfInputs (∑ j : Fin m, s (j.natAdd n)) 0
          (∑ j : Fin n, s (j.castAdd m))) ≫
      eqToHom (congrArg P.arity (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_sum_splitAt n m s).symm) := by
  rw [P.composition_after_first_blocks m n s]
  erw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep_middle]
  simp only [tensorHom_id, Category.assoc]

/-- 概要：単位因子を含まない先頭演算と後半の演算族から全合成を計算する（Berger–Moerdijk §1）。
方針：先頭分解の入力へ逆のテンソル分離と単位子を前置し、逆射を相殺する。
規約：先頭の演算と後半の族のテンソル積を始域とする。
使われ方：先頭ブロックを一つの演算へまとめた計算を外側の全合成へ戻す。 -/
lemma composition_head_without_unit (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (m : ℕ) (s : Fin (1 + m) → ℕ) :
    (P.arity (1 + m) ◁
      (((ρ_ (P.arity (s ((0 : Fin 1).castAdd m)))).inv ▷
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily m (fun j => P.arity (s (j.natAdd 1)))) ≫
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitAt 1 m (fun j => P.arity (s j))).inv)) ≫
      P.composition (1 + m) s =
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep (P.composeAfterInputsFlat 1 m 0 (fun j => s (j.natAdd 1)))
      (P.composeAheadOfInputs (∑ j : Fin m, s (j.natAdd 1)) 0 (s ((0 : Fin 1).castAdd m))) ≫
      eqToHom (congrArg P.arity (by
        have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_sum_splitAt 1 m s
        simpa only [Fin.sum_univ_one] using h.symm :
          s ((0 : Fin 1).castAdd m) + (∑ j : Fin m, s (j.natAdd 1)) = ∑ j, s j)) := by
  rw [P.composition_head_factor m s]
  simp only [whiskerLeft_comp, Category.assoc]
  simp only [← whiskerLeft_comp_assoc, Iso.inv_hom_id_assoc]
  simp only [← comp_whiskerRight, Iso.inv_hom_id,
    id_whiskerRight, whiskerLeft_id, Category.id_comp]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
