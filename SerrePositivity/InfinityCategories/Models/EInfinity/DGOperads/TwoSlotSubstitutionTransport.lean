module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionLastSwap

/-!
模型。文献の定義との比較は後で
# 二位置への代入の入力データの移送

概要：Berger–Moerdijk §1 の末尾交換後の入力族と二入力の arity を、元の前半と逆順の二入力へ移す。
方針：等しい入力データの代入射を共通の始域・終域へ移して比較する。
規約：外側の arity は (n+k)+2、残りの合成の尾は (k+a)+b。
使われ方：交換後の反復合成の因子分解を、証明済みの分離後の外側等変性へ接続する。
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

/-- 概要：末尾二入力の代入後の尾の表記は全入力の arity の和と一致する（Berger–Moerdijk §1）。
方針：有限和を末尾二入力で分解して自然数の加法を整理する。
規約：元の未代入入力 k 個を含む。
使われ方：反復合成の因子分解の最後の arity の移送を指定する。 -/
lemma lastTwoComposeOutput_eq (n k : ℕ) (s : Fin (n + 2) → ℕ) :
    (∑ i : Fin n, s i.castSucc.castSucc) +
        ((k + s (Fin.last n).castSucc) + s (Fin.last (n + 1))) = (∑ i, s i) + k := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_sum_lastTwo n s]
  omega

/-- 概要：交換した末尾二入力の代入後の尾の表記は交換後の全入力の和と一致する（Berger–Moerdijk §1）。
方針：交換後の有限和を末尾二入力で分解し、最後の隣接互換を評価する。
規約：前半の入力は元の族の順序で記述する。
使われ方：交換後の代入射の終域を元の前半と逆順の二入力で表す。 -/
lemma lastTwoSwapOutput_eq (n k : ℕ) (s : Fin (n + 2) → ℕ) :
    (∑ i : Fin n, s i.castSucc.castSucc) +
        ((k + s (Fin.last (n + 1))) + s (Fin.last n).castSucc) =
      (∑ i, s (adjacentTransposition (Fin.last n) i)) + k := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_sum_lastTwo n (fun i => s (adjacentTransposition (Fin.last n) i))]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.adjacentLast_prefix, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.adjacentLast_penultimate, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.adjacentLast_last]
  omega

namespace Operad

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeFirstInputsAfterTwo _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.twoSlotComposition

/-- 概要：等しい arity と前半の入力族の二位置への代入射は移送後に一致する（Berger–Moerdijk §1）。
方針：三つの入力データの等式で置き換え、等式の証明の一意性を使う。
規約：共通の始域 D と終域 T を明示する。
使われ方：交換後の実際の二入力の arity と前半の入力族を正規化する。 -/
lemma twoSlotSubstitution_compare (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n k : ℕ)
    {a a' b b' : ℕ} (ha : a = a') (hb : b = b')
    {s t : Fin n → ℕ} (hs : s = t) {D T : Complex A}
    (hd : P.arity ((n + k) + 2) ⊗
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => P.arity (s i)) ⊗ (P.arity a ⊗ P.arity b)) = D)
    (hd' : P.arity ((n + k) + 2) ⊗
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => P.arity (t i)) ⊗ (P.arity a' ⊗ P.arity b')) = D)
    (ht : P.arity ((∑ i, s i) + ((k + a) + b)) = T)
    (ht' : P.arity ((∑ i, t i) + ((k + a') + b')) = T) :
    eqToHom hd.symm ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep
        (P.twoSlotComposition (n + k) a b ⟨n, by omega⟩ ⟨n + 1, by omega⟩
          (by change n < n + 1; omega))
        (P.composeFirstInputsAfterTwo n k a b s) ≫ eqToHom ht =
      eqToHom hd'.symm ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep
        (P.twoSlotComposition (n + k) a' b' ⟨n, by omega⟩ ⟨n + 1, by omega⟩
          (by change n < n + 1; omega))
        (P.composeFirstInputsAfterTwo n k a' b' t) ≫ eqToHom ht' := by
  subst a'
  subst b'
  subst t
  rfl

/-- 概要：交換後の二位置への代入射は分離の終域の移送後の正規化した代入射に一致する（Berger–Moerdijk §1）。
方針：末尾交換で前半と二位置を評価し、入力データの移送の比較を適用する。
規約：終域は交換後の全入力の arity の和を保つ。
使われ方：交換後の反復合成の因子分解へ、分離後の外側等変性を適用する。 -/
lemma twoSlotSubstitution_lastSwap_transport (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n k : ℕ)
    (s : Fin (n + 2) → ℕ) :
    let w := fun i => s (adjacentTransposition (Fin.last n) i)
    let a := s (Fin.last n).castSucc
    let b := s (Fin.last (n + 1))
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep
        (P.twoSlotComposition (n + k) (w (Fin.last n).castSucc) (w (Fin.last (n + 1)))
          ⟨n, by omega⟩ ⟨n + 1, by omega⟩ (by change n < n + 1; omega))
        (P.composeFirstInputsAfterTwo n k (w (Fin.last n).castSucc)
          (w (Fin.last (n + 1))) (fun i => w i.castSucc.castSucc)) ≫
        eqToHom (congrArg P.arity (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.lastTwoComposeOutput_eq n k w)) =
      (P.arity ((n + k) + 2) ◁
        eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_lastSwap_output_obj n (fun i => P.arity (s i)))) ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep
          (P.twoSlotComposition (n + k) b a ⟨n, by omega⟩ ⟨n + 1, by omega⟩
            (by change n < n + 1; omega))
          (P.composeFirstInputsAfterTwo n k b a (fun i => s i.castSucc.castSucc)) ≫
        eqToHom (congrArg P.arity (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.lastTwoSwapOutput_eq n k s)) := by
  dsimp only
  have ha : s (adjacentTransposition (Fin.last n) (Fin.last n).castSucc) =
      s (Fin.last (n + 1)) := congrArg s (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.adjacentLast_penultimate n)
  have hb : s (adjacentTransposition (Fin.last n) (Fin.last (n + 1))) =
      s (Fin.last n).castSucc := congrArg s (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.adjacentLast_last n)
  have hs : (fun i : Fin n => s (adjacentTransposition (Fin.last n) i.castSucc.castSucc)) =
      (fun i => s i.castSucc.castSucc) := by
    funext i
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.adjacentLast_prefix]
  have h := P.twoSlotSubstitution_compare n k ha hb hs
    (Eq.refl _) (congrArg (fun X : Complex A => P.arity ((n + k) + 2) ⊗ X)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_lastSwap_output_obj n (fun i => P.arity (s i))).symm)
    (congrArg P.arity (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.lastTwoComposeOutput_eq n k
      (fun i => s (adjacentTransposition (Fin.last n) i))))
    (congrArg P.arity (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.lastTwoSwapOutput_eq n k s))
  simpa only [eqToHom_refl, Category.id_comp, whiskerLeft_eqToHom] using h

end Operad

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
