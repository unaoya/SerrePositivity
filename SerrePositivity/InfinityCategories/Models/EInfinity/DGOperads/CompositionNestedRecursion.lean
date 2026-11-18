module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionNestedTransport
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.OneSlotSubstitutionTransport

/-!
模型。文献の定義との比較は後で
# 入れ子の反復合成の再帰の比較

概要：Berger–Moerdijk §1 の一段の挿入と残りの反復合成の結合則を同じ arity へ移す。
方針：尾の括弧付けの移送を相殺し、前半の結合則を全入力の総和へ後合成する。
規約：帰納仮定は通常の等式の引数として渡す。
使われ方：任意の入力数に対する入れ子の反復合成の帰納段階を構成する。
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

attribute [local implicit_reducible] SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeFirstInputs _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeFirstInputInsertion _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeIntoFirst

/-- 概要：外側合成と一段の挿入の結合則を更新前の尾の括弧付けで表す（Berger–Moerdijk §1）。
方針：既存の一段の結合則に出力の移送の逆射を後合成する。
規約：出力は n+((m+k)+l) とする。
使われ方：有限族の入れ子の代入の比較の最初の仮定を満たす。 -/
lemma composeIntoFirst_insertion_raw (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (m n k l : ℕ) :
    (P.composeIntoFirst m (n + 1) k ▷ P.arity l) ≫ P.composeFirstInputInsertion n (m + k) l =
    (α_ (P.arity (m + 1)) (P.arity (n + 1 + k)) (P.arity l)).hom ≫
      (P.arity (m + 1) ◁ P.composeFirstInputInsertion n k l) ≫
        P.composeIntoFirst m n (k + l) ≫
          eqToHom (congrArg P.arity (by omega : n + (m + (k + l)) = n + ((m + k) + l))) := by
  have h := congrArg (· ≫ eqToHom (congrArg P.arity
    (by omega : n + (m + (k + l)) = n + ((m + k) + l))))
      (P.composeIntoFirst_insertion m n k l)
  simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using h

/-- 概要：前半の入れ子の結合則を最後の入力の代入後の arity へ移す（Berger–Moerdijk §1）。
方針：尾の結合則で反復合成を移送し、帰納仮定の出力を全入力の総和へ直す。
規約：最後の入力の長さは s(last n) とする。
使われ方：有限族の入れ子の代入の比較の残りの反復合成の仮定を満たす。 -/
lemma composeIntoFirst_prefix_nested (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (m n k : ℕ) (s : Fin (n + 1) → ℕ)
    (hprefix :
      (P.composeIntoFirst m n (k + s (Fin.last n)) ▷
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => P.arity (s j.castSucc))) ≫
        P.composeFirstInputs n (m + (k + s (Fin.last n))) (fun j => s j.castSucc) =
      (α_ (P.arity (m + 1)) (P.arity (n + (k + s (Fin.last n))))
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => P.arity (s j.castSucc)))).hom ≫
        (P.arity (m + 1) ◁ P.composeFirstInputs n (k + s (Fin.last n))
          (fun j => s j.castSucc)) ≫
        P.composeIntoFirst m (∑ j : Fin n, s j.castSucc) (k + s (Fin.last n))) :
    ((P.composeIntoFirst m n (k + s (Fin.last n)) ≫
      eqToHom (congrArg P.arity (by omega : n + (m + (k + s (Fin.last n))) =
        n + ((m + k) + s (Fin.last n))))) ▷
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => P.arity (s j.castSucc))) ≫
      P.composeFirstInputs n ((m + k) + s (Fin.last n)) (fun j => s j.castSucc) ≫
        eqToHom (congrArg P.arity (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.oneSlotComposeOutput_eq n (m + k) s)) =
    (α_ (P.arity (m + 1)) (P.arity (n + (k + s (Fin.last n))))
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => P.arity (s j.castSucc)))).hom ≫
      (P.arity (m + 1) ◁ (P.composeFirstInputs n (k + s (Fin.last n))
        (fun j => s j.castSucc) ≫ eqToHom (congrArg P.arity (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.oneSlotComposeOutput_eq n k s)))) ≫
        P.composeIntoFirst m (∑ j, s j) k := by
  have hi := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.oneSlotComposeOutput_eq n k s
  have ht : (∑ j : Fin n, s j.castSucc) + (m + (k + s (Fin.last n))) =
      (∑ j, s j) + (m + k) := by omega
  rw [comp_whiskerRight, Category.assoc,
    P.composeFirstInputs_tail_cast_assoc n (Nat.add_assoc m k (s (Fin.last n))).symm
      (fun j => s j.castSucc), eqToHom_trans]
  have h := congrArg (· ≫ eqToHom (congrArg P.arity ht)) hprefix
  simp only [Category.assoc] at h
  conv_rhs at h =>
    arg 2
    arg 2
    rw [← P.composeIntoFirst_index_eq m (∑ j : Fin n, s j.castSucc) (k + s (Fin.last n))
      (∑ j, s j) k hi]
  simp only [← whiskerLeft_comp_assoc] at h
  exact h

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
