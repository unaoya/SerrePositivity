module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.IteratedOperationSplitLast
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyPowerTailSplitLast
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorLastPairSeparation
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionAdjacentFactor

/-!
模型。文献の定義との比較は後で
# 末尾入力付き反復合成のテンソル射の再帰

概要：Berger–Moerdijk §1 の反復合成を最後の演算から処理する再帰をテンソル射全体で示す。
方針：最後の演算を分離し、係数の再帰と入力の三ブロック連結を同時に適用する。
規約：最後の演算の入力を既存の末尾の前に置き、新しい末尾の長さを k+l と書く。
使われ方：任意の代数での全合成の評価の帰納段階に用いる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
open scoped _root_.BigOperators

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily _root_.SerrePositivity.TensorPowers.power
  SerrePositivity.SymmetricSequence SerrePositivity.SymmetricSequence.level
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：反復合成のテンソル射は最後の係数の部分合成と残りの反復合成に分かれる（Berger–Moerdijk §1）。
方針：係数と入力を分離する式へそれぞれの再帰を適用し、最後の係数を取り出す比較式を使う。
規約：新しい末尾は最後の演算の入力と元の末尾の順で並ぶ。
使われ方：代数の全合成の評価を長さ n の帰納仮定と部分合成則から証明する。 -/
lemma iteratedOperationTensor_succ (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (K : Complex A)
    (n k : ℕ) (s : Fin (n + 1) → ℕ) :
    let R := P.arity (n + 1 + k)
    let D := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => P.arity (s j.castSucc) ⊗ power K (s j.castSucc))
    let l := s (Fin.last n)
    (R ◁ ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n (fun j => P.arity (s j) ⊗ power K (s j))).inv ▷
      power K k)) ≫ P.iteratedOperationTensor K (n + 1) k s =
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorLastPairExtraction R D (P.arity l) (power K l) (power K k) ≫
      (P.composeFirstInputInsertion n k l ⊗ₘ
        (D ◁ ((appendIso K l k).hom ≫
          eqToHom (congrArg (power K) (Nat.add_comm l k))))) ≫
      P.iteratedOperationTensor K n (k + l) (fun j => s j.castSucc) ≫
      (eqToHom (congrArg P.arity (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.oneSlotComposeOutput_eq n k s)) ⊗ₘ
        eqToHom (congrArg (power K) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.oneSlotComposeOutput_eq n k s))) := by
  dsimp only
  have hc : (P.arity (n + 1 + k) ◁
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n (fun j => P.arity (s j))).inv) ≫
      P.composeFirstInputs (n + 1) k s =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep (P.composeFirstInputInsertion n k (s (Fin.last n)))
        (P.composeFirstInputs n (k + s (Fin.last n)) (fun j => s j.castSucc)) ≫
        eqToHom (congrArg P.arity (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.oneSlotComposeOutput_eq n k s)) := by
    rw [P.composeFirstInputs_oneSlot_after_factor]
    simp only [← whiskerLeft_comp_assoc, Iso.inv_hom_id, whiskerLeft_id, Category.id_comp]
  rw [P.iteratedOperationTensor_splitLast, hc,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyTail_splitLast_inv_cast K n k s (Nat.add_comm (s (Fin.last n)) k)]
  let b := (appendIso K (s (Fin.last n)) k).hom ≫
    eqToHom (congrArg (power K) (Nat.add_comm (s (Fin.last n)) k))
  let a := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K n (fun j => s j.castSucc)).hom
  let c := (appendIso K (∑ j : Fin n, s j.castSucc) (k + s (Fin.last n))).hom
  have ht := (tensorHom_comp_tensorHom
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep (P.composeFirstInputInsertion n k (s (Fin.last n)))
      (P.composeFirstInputs n (k + s (Fin.last n)) (fun j => s j.castSucc)))
    ((α_ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => power K (s j.castSucc)))
      (power K (s (Fin.last n))) (power K k)).hom ≫ (a ⊗ₘ b) ≫ c)
    (eqToHom (congrArg P.arity (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.oneSlotComposeOutput_eq n k s)))
    (eqToHom (congrArg (power K) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.oneSlotComposeOutput_eq n k s)))).symm
  simp only [Category.assoc] at ht
  rw [ht]
  erw [reassoc_of% (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorLastPairIteration
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso n (fun j => P.arity (s j.castSucc))
      (fun j => power K (s j.castSucc))).hom
    (P.composeFirstInputInsertion n k (s (Fin.last n)))
    (P.composeFirstInputs n (k + s (Fin.last n)) (fun j => s j.castSucc)) a b c)]
  rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
