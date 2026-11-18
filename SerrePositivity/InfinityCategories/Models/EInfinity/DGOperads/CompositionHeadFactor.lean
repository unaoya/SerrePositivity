module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionOneAhead
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionBlockTheorem

/-!
模型。文献の定義との比較は後で
# 全入力への合成を後半の反復合成と先頭合成へ分解する

概要：Berger–Moerdijk §1 の部分合成則で、外側の後半の演算を合成してから先頭へ代入する。
方針：二ブロック分解の前半を一入力とし、一次テンソルの単位因子を除く。
規約：先頭の添字は Fin 1 から castAdd で埋め込み、後半は natAdd を使う。
使われ方：平行な交換則と入れ子の結合則で得た係数の合成を全合成へ戻す。
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

/-- 概要：全入力への合成は後半の有限族への代入と先頭への部分合成で計算できる（Berger–Moerdijk §1）。
方針：前半一入力の二ブロック分解に、一入力への反復合成の先頭合成の式を適用する。
規約：先頭の arity は s((0 : Fin 1).castAdd m)、後半の総 arity は natAdd の族の和。
使われ方：Schur 作用の部分合成則の外側の係数の合成を再構成する。 -/
lemma composition_head_factor (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (m : ℕ) (s : Fin (1 + m) → ℕ) :
    P.composition (1 + m) s =
    (P.arity (1 + m) ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitAt 1 m (fun j => P.arity (s j))).hom) ≫
      (P.arity (1 + m) ◁ ((ρ_ (P.arity (s ((0 : Fin 1).castAdd m)))).hom ▷
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily m (fun j => P.arity (s (j.natAdd 1))))) ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep (P.composeAfterInputsFlat 1 m 0 (fun j => s (j.natAdd 1)))
        (P.composeAheadOfInputs (∑ j : Fin m, s (j.natAdd 1)) 0 (s ((0 : Fin 1).castAdd m))) ≫
      eqToHom (congrArg P.arity (by
        have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_sum_splitAt 1 m s
        simpa only [Fin.sum_univ_one] using h.symm :
          s ((0 : Fin 1).castAdd m) + (∑ j : Fin m, s (j.natAdd 1)) = ∑ j, s j)) := by
  rw [P.composition_eq_blocks 1 m s]
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeByBlocks
  rw [P.composeFirstInputs_one_ahead]
  erw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep_middle]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep_post]
  simp only [tensorHom_id, Category.assoc, eqToHom_trans]
  rw [P.composeAfterInputsFlat_zero_tail]
  rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
