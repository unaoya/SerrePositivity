module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionAheadParallelRecursion

/-!
模型。文献の定義との比較は後で
# 先頭の部分合成と後半の有限族への代入の交換

概要：Berger–Moerdijk §1 の異なる入力への代入の交換則を任意の有限入力族へ拡張する。
方針：後半の長さで帰納し、一段の平行な部分合成と残りの代入の交換則を結合する。
規約：先頭へ p 入力の演算を合成し、その後の m 入力へ指定した演算を代入する。
使われ方：全入力への合成の二ブロック分解をオペラッドの部分合成則へ接続する。
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
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeAfterInputsFlat _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeAheadOfInputs _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySubstitutionStep

/-- 概要：先頭への部分合成は後半の任意の有限演算族への反復代入と交換できる（Berger–Moerdijk §1）。
方針：空の族の基底と、一段の交換則を有限族のテンソル代入へ持ち上げる補題で帰納する。
規約：p=0、空の後半、arity 0 の後半の演算をすべて許す。
使われ方：自由代数の部分合成則の係数側で、外側の残りの入力への代入を先に行う。 -/
lemma composeAheadOfInputs_after_parallel (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (m k p : ℕ) (s : Fin m → ℕ) :
    (P.composeAheadOfInputs m k p ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily m (fun j => P.arity (s j))) ≫
      P.composeAfterInputsFlat p m k s =
    (α_ (P.arity (1 + m + k)) (P.arity p) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily m (fun j => P.arity (s j)))).hom ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep (P.composeAfterInputsFlat 1 m k s)
        (P.composeAheadOfInputs (∑ j, s j) k p) := by
  induction m generalizing k with
  | zero => exact P.composeAheadOfInputs_after_zero k p s
  | succ m ih =>
    have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySubstitutionStep_parallel m (fun j => P.arity (s j))
      (P.composeAheadOfInputs (m + 1) k p)
      (P.composeFirstInputInsertion (1 + m) k (s (Fin.last m)))
      (P.composeFirstInputInsertion (p + m) k (s (Fin.last m)))
      (P.composeAheadOfInputs m (k + s (Fin.last m)) p)
      (P.composeAfterInputsFlat p m (k + s (Fin.last m)) (fun j => s j.castSucc) ≫
        eqToHom (congrArg P.arity (by
          have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.oneSlotComposeOutput_eq m k s
          omega : p + (∑ j : Fin m, s j.castSucc) + (k + s (Fin.last m)) = p + (∑ j, s j) + k)))
      (P.composeAfterInputsFlat 1 m (k + s (Fin.last m)) (fun j => s j.castSucc) ≫
        eqToHom (congrArg P.arity (by
          have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.oneSlotComposeOutput_eq m k s
          omega : 1 + (∑ j : Fin m, s j.castSucc) + (k + s (Fin.last m)) = 1 + (∑ j, s j) + k)))
      (P.composeAheadOfInputs (∑ j, s j) k p)
      (P.composeAheadOfInputs_parallel m k p (s (Fin.last m)))
      (P.composeAheadOfInputs_after_prefix m k p s
        (ih (k + s (Fin.last m)) (fun j => s j.castSucc)))
    rw [P.composeAfterInputsFlat_succ p m k s, P.composeAfterInputsFlat_succ 1 m k s]
    exact h

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
