module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionAheadParallelBase

/-!
模型。文献の定義との比較は後で
# 先頭合成と後半の反復代入の帰納仮定の移送

概要：Berger–Moerdijk §1 の代入交換の帰納仮定を、全入力の総 arity の出力へ移す。
方針：短い入力族の交換則へ出力の移送を後合成し、先頭合成の添字の移送を使う。
規約：最後の入力の arity を更新した尾へ加える。
使われ方：先頭合成と後半の有限族への反復代入の交換則の帰納段階を満たす。
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
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeAheadOfInputs _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeAfterInputsFlat _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep

/-- 概要：短い後半の交換則を全入力の arity へ移送する（Berger–Moerdijk §1）。
方針：出力の移送を先頭合成の前へ戻し、テンソル代入の最初の射の後合成へまとめる。
規約：帰納仮定は最後の入力を除いた族と更新した尾について与える。
使われ方：平行な有限族のテンソル代入の比較の残りの代入の仮定となる。 -/
lemma composeAheadOfInputs_after_prefix (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (m k p : ℕ) (s : Fin (m + 1) → ℕ)
    (hprefix :
      (P.composeAheadOfInputs m (k + s (Fin.last m)) p ▷
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily m (fun j => P.arity (s j.castSucc))) ≫
        P.composeAfterInputsFlat p m (k + s (Fin.last m)) (fun j => s j.castSucc) =
      (α_ (P.arity (1 + m + (k + s (Fin.last m)))) (P.arity p)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily m (fun j => P.arity (s j.castSucc)))).hom ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep
          (P.composeAfterInputsFlat 1 m (k + s (Fin.last m)) (fun j => s j.castSucc))
          (P.composeAheadOfInputs (∑ j : Fin m, s j.castSucc) (k + s (Fin.last m)) p)) :
    (P.composeAheadOfInputs m (k + s (Fin.last m)) p ▷
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily m (fun j => P.arity (s j.castSucc))) ≫
      (P.composeAfterInputsFlat p m (k + s (Fin.last m)) (fun j => s j.castSucc) ≫
        eqToHom (congrArg P.arity (by
          have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.oneSlotComposeOutput_eq m k s
          omega : p + (∑ j : Fin m, s j.castSucc) + (k + s (Fin.last m)) = p + (∑ j, s j) + k))) =
    (α_ (P.arity (1 + m + (k + s (Fin.last m)))) (P.arity p)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily m (fun j => P.arity (s j.castSucc)))).hom ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep
        (P.composeAfterInputsFlat 1 m (k + s (Fin.last m)) (fun j => s j.castSucc) ≫
          eqToHom (congrArg P.arity (by
            have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.oneSlotComposeOutput_eq m k s
            omega : 1 + (∑ j : Fin m, s j.castSucc) + (k + s (Fin.last m)) =
              1 + (∑ j, s j) + k)))
        (P.composeAheadOfInputs (∑ j, s j) k p) := by
  have hi := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.oneSlotComposeOutput_eq m k s
  have h := congrArg (· ≫ eqToHom (congrArg P.arity (by
    omega : p + (∑ j : Fin m, s j.castSucc) + (k + s (Fin.last m)) = p + (∑ j, s j) + k)))
      hprefix
  simp only [Category.assoc] at h
  conv_rhs at h =>
    arg 2
    rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep_post]
    rw [← P.composeAheadOfInputs_index_eq (∑ j : Fin m, s j.castSucc)
      (k + s (Fin.last m)) (∑ j, s j) k p hi]
    rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep_first_post]
  exact h

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
