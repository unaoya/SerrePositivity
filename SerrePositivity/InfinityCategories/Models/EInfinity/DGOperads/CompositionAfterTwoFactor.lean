module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionAfterTwoSlots
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionTwoSlot

/-!
模型。文献の定義との比較は後で
# 二位置への合成と残りの反復合成による因子分解

概要：Berger–Moerdijk §1 の末尾二入力の反復合成を、尾の交換に適した因子分解へ直す。
方針：未代入の尾の長さの等式による移送を使い、最後の arity の移送を合成全体の後へ出す。
規約：二位置への合成は末尾二位置に適用し、残りの尾の長さは (k+a)+b とする。
使われ方：二位置への合成と残りの反復合成の外側等変性を組み合わせる。
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
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeFirstInputs _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep

/-- 概要：二入力の代入後の反復合成は尾の長さの順序の異なる表記でも計算できる（Berger–Moerdijk §1）。
方針：尾の長さの等式の可換正方形に始域と終域の移送を合成する。
規約：定義の尾は (k+a)+b、比較する再帰の尾は (k+b)+a。
使われ方：既存の二段の因子分解を尾のブロック交換に適した表記へそろえる。 -/
lemma composeFirstInputsAfterTwo_tail_order (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n k a b : ℕ)
    (s : Fin n → ℕ) :
    P.composeFirstInputsAfterTwo n k a b s =
      (eqToHom (congrArg P.arity
          (by omega : ((n + k) + a) + b = n + ((k + b) + a))) ▷
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => P.arity (s i))) ≫
        P.composeFirstInputs n ((k + b) + a) s ≫
        eqToHom (congrArg P.arity
          (by omega : (∑ i, s i) + ((k + b) + a) = (∑ i, s i) + ((k + a) + b))) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeFirstInputsAfterTwo
  have htail := P.composeFirstInputs_tail_index_eq n
    (by omega : (k + a) + b = (k + b) + a) s
  have h := congrArg (fun (f :
      P.arity (n + ((k + a) + b)) ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => P.arity (s i)) ⟶
        P.arity ((∑ i, s i) + ((k + b) + a))) =>
      (eqToHom (congrArg P.arity
          (by omega : ((n + k) + a) + b = n + ((k + a) + b))) ▷
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => P.arity (s i))) ≫ f ≫
        eqToHom (congrArg P.arity
          (by omega : (∑ i, s i) + ((k + b) + a) = (∑ i, s i) + ((k + a) + b)))) htail
  simp only [Category.assoc] at h
  rw [← comp_whiskerRight_assoc, eqToHom_trans] at h
  simp only [eqToHom_trans, eqToHom_refl, Category.comp_id] at h
  exact h.symm

/-- 概要：末尾二入力の反復合成は二位置への合成と残りの反復合成に因子分解する（Berger–Moerdijk §1）。
方針：既存の二位置への因子分解に尾の長さの比較を使い、終域の移送を外へ出す。
規約：残りの反復合成は尾を (k+a)+b として扱う。
使われ方：末尾交換の外側等変性の二つの可換正方形を接続する。 -/
lemma composeFirstInputs_twoSlot_after_factor (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n k : ℕ)
    (s : Fin (n + 2) → ℕ) :
    let a := s (Fin.last n).castSucc
    let b := s (Fin.last (n + 1))
    P.composeFirstInputs (n + 2) k s =
      (eqToHom (congrArg P.arity (by omega : n + 2 + k = (n + k) + 2)) ▷
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + 2) (fun i => P.arity (s i))) ≫
        (P.arity ((n + k) + 2) ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLastTwo n (fun i => P.arity (s i))).hom) ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep
          (P.twoSlotComposition (n + k) a b ⟨n, by omega⟩ ⟨n + 1, by omega⟩
            (by change n < n + 1; omega))
          (P.composeFirstInputsAfterTwo n k a b (fun i => s i.castSucc.castSucc)) ≫
        eqToHom (congrArg P.arity (by
          dsimp only [a, b]
          rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_sum_lastTwo n s]
          omega : (∑ i : Fin n, s i.castSucc.castSucc) + ((k + a) + b) = (∑ i, s i) + k)) := by
  dsimp only
  rw [P.composeFirstInputs_twoSlot_factor]
  rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep_post]
  rw [P.composeFirstInputsAfterTwo_tail_order]
  simp only [Category.assoc, eqToHom_trans]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
