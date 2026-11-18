module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.NullaryPrefixDelete

/-!
# 零入力への代入と残した入力の置換

## 概要
HA 3.2.4.7 の二色比較の係数射は、消去しない色の置換を出力の置換へ移す。

## 方針
反復合成の尾の等変性に、単位からの係数族の挿入の自然性と arity の移送を適用する。

## 規約
順射は `nullaryPrefixDelete` のまま保持する。

## 使われ方
二色部分群に関する実際の係数射の等変性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory MonoidalCategory
open scoped BigOperators
attribute [local implicit_reducible] SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level
variable (A : Type u) [CommRing A]
attribute [local implicit_reducible] operad sequence

/-- 空の出力ブロックを除いた後の置換は、元の尾の置換である。 -/
lemma nullaryTailPermutation_transport (n k : ℕ) (σ : Equiv.Perm (Fin k))
    (h : (∑ _ : Fin n, 0) + k = k) :
    (finCongr h).permCongr
      (FiniteBijection.blockEquiv (Equiv.refl (Fin (∑ _ : Fin n, 0))) σ) = σ := by
  have hz : (∑ _ : Fin n, 0) = 0 := by simp
  generalize hs : (∑ _ : Fin n, 0) = l at h ⊢
  have hl : l = 0 := hs.symm.trans hz
  clear hs hz
  subst l
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_zero_left, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.finCongr_permCongr_trans]
  rfl

/-- 零入力への代入は、残した尾の任意の置換に関して等変である。 -/
lemma nullaryPrefixDelete_tail_equivariance (n k : ℕ) (σ : Equiv.Perm (Fin k)) :
    (operad A).sequence.map (FiniteBijection.permutation (n + k)
      (FiniteBijection.blockEquiv (Equiv.refl (Fin n)) σ)) ≫ nullaryPrefixDelete A n k =
      nullaryPrefixDelete A n k ≫
        (operad A).sequence.map (FiniteBijection.permutation k σ) := by
  let hsum : (∑ _ : Fin n, 0) + k = k := by simp
  let t := eqToHom (congrArg (operad A).arity hsum)
  have h := (operad A).composeFirstInputs_tail_equivariance n k (fun _ => 0) σ
  have ht := (operad A).arity_permutation_index_eq hsum
    (FiniteBijection.blockEquiv (Equiv.refl (Fin (∑ _ : Fin n, 0))) σ)
  rw [nullaryTailPermutation_transport] at ht
  unfold nullaryPrefixDelete
  erw [coefficientUnitInsert_naturality_assoc]
  have h₁ := congrArg
    (fun c => coefficientUnitInsert _ _ (nullaryInputFamily A n) ≫ c ≫ t) h
  have h₂ := congrArg
    (fun c => coefficientUnitInsert _ _ (nullaryInputFamily A n) ≫
      (operad A).composeFirstInputs n k (fun _ => 0) ≫ c) ht.symm
  dsimp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.arity, SerrePositivity.SymmetricSequence.level] at h₁ h₂ ⊢
  simp only [Category.assoc] at h₁ h₂
  simpa only [Category.assoc] using h₁.trans h₂

end SerrePositivity.EInfinity.BarrattEccles
