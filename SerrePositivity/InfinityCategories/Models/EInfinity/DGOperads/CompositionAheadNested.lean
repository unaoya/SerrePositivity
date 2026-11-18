module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionAhead
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionNested

/-!
模型。文献の定義との比較は後で
# 後方の入力を残す先頭合成と内側の全入力への代入

概要：Berger–Moerdijk §1 の入れ子の結合則を先頭合成の arity の表記へ移す。
方針：先頭合成を composeIntoFirst で表し、内側の反復合成の結合則を適用する。
規約：外側の残る m+k 入力の順序を保ち、内側の入力を全て合成する。
使われ方：後半との平行な交換則と入れ子の結合則を接続する。
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

/-- 概要：後方を残す先頭合成を反復合成で使う先頭合成へ移す（Berger–Moerdijk §1）。
方針：二つの定義の部分合成を同一視し、出力の arity の移送をまとめる。
規約：外側の arity は 1+m+k、内側は n。
使われ方：先頭合成に入れ子の反復合成の結合則を適用する。 -/
lemma composeAheadOfInputs_to_first (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (m k n : ℕ) :
    P.composeAheadOfInputs m k n ≫
      eqToHom (congrArg P.arity (Nat.add_assoc n m k)) =
    (eqToHom (congrArg P.arity (by omega : 1 + m + k = (m + k) + 1)) ▷ P.arity n) ≫
      P.composeIntoFirst (m + k) n 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeAheadOfInputs _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeIntoFirst
  simp only [Nat.add_zero, Category.assoc, eqToHom_trans]

/-- 概要：反復合成で使う先頭合成を後方を残す arity の表記へ戻す（Berger–Moerdijk §1）。
方針：二つの先頭合成の定義を展開し、出力の移送をまとめる。
規約：前方と後方の長さの表記だけを移し、入力の置換を加えない。
使われ方：入れ子の結合則の出力を composeAheadOfInputs に戻す。 -/
@[reassoc]
lemma composeAheadOfInputs_from_first (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (m k n : ℕ) :
    (eqToHom (congrArg P.arity (by omega : 1 + m + k = (m + k) + 1)) ▷ P.arity n) ≫
      P.composeIntoFirst (m + k) n 0 ≫
        eqToHom (congrArg P.arity (Nat.add_assoc n m k).symm) =
    P.composeAheadOfInputs m k n := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeAheadOfInputs _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeIntoFirst
  simp only [Nat.add_zero, Category.assoc, eqToHom_trans]

/-- 概要：先頭入力へ合成してから内側の全入力へ代入する計算は入れ子の結合則を満たす（Berger–Moerdijk §1）。
方針：先頭合成を既存の入れ子の反復合成へ移し、外側 arity の移送を自然性で前後へ通す。
規約：外側の残る m+k 入力を保ち、出力を (∑ s)+m+k で表す。
使われ方：Schur 作用の部分合成則の係数側の内側入力の合成を処理する。 -/
lemma composeAheadOfInputs_nested (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (m k n : ℕ) (s : Fin n → ℕ) :
    (P.composeAheadOfInputs m k n ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => P.arity (s j))) ≫
      (eqToHom (congrArg P.arity (Nat.add_assoc n m k)) ▷
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => P.arity (s j))) ≫
      P.composeFirstInputs n (m + k) s ≫
        eqToHom (congrArg P.arity (Nat.add_assoc (∑ j, s j) m k).symm) =
    (α_ (P.arity (1 + m + k)) (P.arity n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => P.arity (s j)))).hom ≫
      (P.arity (1 + m + k) ◁ P.composition n s) ≫
        P.composeAheadOfInputs m k (∑ j, s j) := by
  rw [← comp_whiskerRight_assoc, P.composeAheadOfInputs_to_first m k n]
  simp only [comp_whiskerRight, Category.assoc]
  erw [reassoc_of% (P.composeIntoFirst_nested (m + k) n 0 s)]
  erw [associator_naturality_left_assoc, ← whisker_exchange_assoc]
  erw [P.composeAheadOfInputs_from_first m k (∑ j, s j)]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composition, eqToHom_refl, id_whiskerRight, Category.id_comp, Category.comp_id]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
