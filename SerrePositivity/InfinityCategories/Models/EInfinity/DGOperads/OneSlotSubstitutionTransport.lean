module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.IteratedCompositionEquivariance
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilySplitLastTransport

/-!
模型。文献の定義との比較は後で
# 最後の入力への代入と入力データの移送

概要：Berger–Moerdijk §1 の末尾を固定する交換後の反復合成の入力データを正規化する。
方針：最後の arity と前半の入力族の等式を、共通の始域と終域への移送で比較する。
規約：最後の入力から代入し、残りの尾の長さを k+l とする。
使われ方：隣接交換後の反復合成の再帰を元の前半の交換へ帰着する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.Coxeter
open scoped _root_.BigOperators

/-- 概要：最後の入力を代入した後の尾の表記は全入力の arity の和に一致する（Berger–Moerdijk §1）。
方針：有限和を最後の入力で分解して自然数の加法を整理する。
規約：未代入入力 k 個を含める。
使われ方：反復合成の再帰の最後の arity の移送を指定する。 -/
lemma oneSlotComposeOutput_eq (n k : ℕ) (s : Fin (n + 1) → ℕ) :
    (∑ j : Fin n, s j.castSucc) + (k + s (Fin.last n)) = (∑ j, s j) + k := by
  rw [Fin.sum_univ_castSucc s]
  omega

/-- 概要：末尾固定の交換後の全入力の和は交換した前半と元の最後の arity で表せる（Berger–Moerdijk §1）。
方針：交換後の有限和を最後で分解し、持ち上げた隣接互換を評価する。
規約：交換位置は i.castSucc。
使われ方：交換後の残りの反復合成の出力を全入力の和へ移す。 -/
lemma oneSlotSwapOutput_eq (n k : ℕ) (s : Fin (n + 2) → ℕ) (i : Fin n) :
    (∑ j : Fin (n + 1), s (adjacentTransposition i j).castSucc) +
        (k + s (Fin.last (n + 1))) =
      (∑ j, s (adjacentTransposition i.castSucc j)) + k := by
  rw [Fin.sum_univ_castSucc (fun j => s (adjacentTransposition i.castSucc j))]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.adjacentCastSucc_prefix, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.adjacentCastSucc_last]
  omega

namespace Operad

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeFirstInputInsertion _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeFirstInputs

/-- 概要：等しい最後の arity と前半の入力族の代入射は共通の対象への移送後に一致する（Berger–Moerdijk §1）。
方針：二つの入力データの等式で置き換え、等式の証明の一意性を使う。
規約：共通の始域 D と終域 T を明示する。
使われ方：末尾固定の交換後の代入射の入力データを正規化する。 -/
lemma oneSlotSubstitution_compare (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n k : ℕ)
    {l m : ℕ} (hl : l = m) {s t : Fin n → ℕ} (hs : s = t) {D T : Complex A}
    (hd : P.arity (n + 1 + k) ⊗
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => P.arity (s j)) ⊗ P.arity l) = D)
    (hd' : P.arity (n + 1 + k) ⊗
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => P.arity (t j)) ⊗ P.arity m) = D)
    (ht : P.arity ((∑ j, s j) + (k + l)) = T)
    (ht' : P.arity ((∑ j, t j) + (k + m)) = T) :
    eqToHom hd.symm ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep (P.composeFirstInputInsertion n k l)
        (P.composeFirstInputs n (k + l) s) ≫ eqToHom ht =
      eqToHom hd'.symm ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep (P.composeFirstInputInsertion n k m)
        (P.composeFirstInputs n (k + m) t) ≫ eqToHom ht' := by
  subst m
  subst t
  rfl

/-- 概要：末尾固定の交換後の代入射は分離の終域を移した元の最後の arity の代入射に一致する（Berger–Moerdijk §1）。
方針：交換後の最後の arity と前半の族を評価し、入力データの移送の比較を適用する。
規約：終域は交換後の全入力の和とする。
使われ方：交換後の反復合成の因子分解へ帰納仮定を適用できる形にする。 -/
lemma oneSlotSubstitution_adjacent_transport (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n k : ℕ)
    (s : Fin (n + 2) → ℕ) (i : Fin n) :
    let w := fun j => s (adjacentTransposition i.castSucc j)
    let l := s (Fin.last (n + 1))
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep (P.composeFirstInputInsertion (n + 1) k (w (Fin.last (n + 1))))
        (P.composeFirstInputs (n + 1) (k + w (Fin.last (n + 1))) (fun j => w j.castSucc)) ≫
        eqToHom (congrArg P.arity (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.oneSlotComposeOutput_eq (n + 1) k w)) =
      (P.arity (n + 2 + k) ◁
        eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_adjacentCastSucc_output_obj n (fun j => P.arity (s j)) i)) ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep (P.composeFirstInputInsertion (n + 1) k l)
          (P.composeFirstInputs (n + 1) (k + l)
            (fun j => s (adjacentTransposition i j).castSucc)) ≫
        eqToHom (congrArg P.arity (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.oneSlotSwapOutput_eq n k s i)) := by
  dsimp only
  have hl : s (adjacentTransposition i.castSucc (Fin.last (n + 1))) =
      s (Fin.last (n + 1)) := congrArg s (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.adjacentCastSucc_last n i)
  have hs : (fun j : Fin (n + 1) => s (adjacentTransposition i.castSucc j.castSucc)) =
      (fun j => s (adjacentTransposition i j).castSucc) := by
    funext j
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.adjacentCastSucc_prefix]
  have h := P.oneSlotSubstitution_compare (n + 1) k hl hs
    (Eq.refl _) (congrArg (fun X : Complex A => P.arity (n + 2 + k) ⊗ X)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_adjacentCastSucc_output_obj n (fun j => P.arity (s j)) i).symm)
    (congrArg P.arity (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.oneSlotComposeOutput_eq (n + 1) k
      (fun j => s (adjacentTransposition i.castSucc j))))
    (congrArg P.arity (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.oneSlotSwapOutput_eq n k s i))
  simpa only [eqToHom_refl, Category.id_comp, whiskerLeft_eqToHom] using h

end Operad

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
