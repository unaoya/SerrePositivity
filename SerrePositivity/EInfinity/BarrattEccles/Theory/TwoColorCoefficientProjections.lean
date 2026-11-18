module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.NullaryPrefixTail
public import SerrePositivity.EInfinity.BarrattEccles.Theory.TwoColorCoefficientSource
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.BinarySlotSwap

/-!
# 二色の係数への指定射影

## 概要
HA 3.2.4.7 の二色比較で使う、二つの色の係数への実際の射影を構成する。

## 方針
零入力への代入とブロック交換を使い、ブロック内の両方の置換を追跡する。

## 規約
右側の色は先頭を消去し、左側の色はブロック交換してから先頭を消去する。

## 使われ方
Hopf 対角の後に適用する二色の係数比較の二つの因子。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory MonoidalCategory
attribute [local implicit_reducible] SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level

/-- 二色のブロック交換は、各ブロック内の置換を逆の順の二色へ移す。 -/
lemma twoColorBlockSwap_naturality (m n : ℕ)
    (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)) :
    (FiniteBijection.blockEquiv σ τ).trans (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap m n) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap m n).trans (FiniteBijection.blockEquiv τ σ) := by
  apply Equiv.ext
  intro x
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective x
  cases x with
  | inl x =>
    change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap m n (FiniteBijection.blockEquiv σ τ (x.castAdd n)) =
      FiniteBijection.blockEquiv τ σ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap m n (x.castAdd n))
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_apply_left, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap_left,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap_left, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_apply_right]
  | inr x =>
    change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap m n (FiniteBijection.blockEquiv σ τ (x.natAdd m)) =
      FiniteBijection.blockEquiv τ σ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap m n (x.natAdd m))
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_apply_right, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap_right,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap_right, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_apply_left]

/-- ブロック交換の自然性を、オペラッドの実際の係数射へ移す。 -/
lemma coefficientBlockSwap_naturality {A : Type u} [CommRing A] (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A)
    (m n : ℕ) (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)) :
    P.sequence.map (FiniteBijection.permutation (m + n) (FiniteBijection.blockEquiv σ τ)) ≫
      P.arityBijectionMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap m n) =
        P.arityBijectionMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap m n) ≫
          P.sequence.map
            (FiniteBijection.permutation (n + m) (FiniteBijection.blockEquiv τ σ)) := by
  change P.arityBijectionMap (FiniteBijection.blockEquiv σ τ) ≫ _ =
    _ ≫ P.arityBijectionMap (FiniteBijection.blockEquiv τ σ)
  rw [← P.arityBijectionMap_trans, ← P.arityBijectionMap_trans, twoColorBlockSwap_naturality]

namespace BarrattEccles
variable (A : Type u) [CommRing A]
attribute [local implicit_reducible] operad sequence

/-- 零入力への代入は二色の任意のブロック内置換に関して等変である。 -/
lemma nullaryPrefixDelete_block_equivariance (m n : ℕ)
    (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)) :
    (operad A).sequence.map
      (FiniteBijection.permutation (m + n) (FiniteBijection.blockEquiv σ τ)) ≫
        nullaryPrefixDelete A m n = nullaryPrefixDelete A m n ≫
          (operad A).sequence.map (FiniteBijection.permutation n τ) := by
  have he : FiniteBijection.blockEquiv σ τ =
      FiniteBijection.blockEquiv σ (Equiv.refl (Fin n)) *
        FiniteBijection.blockEquiv (Equiv.refl (Fin m)) τ := by
    have h₁ : σ * Equiv.refl (Fin m) = σ := by ext x; rfl
    have h₂ : Equiv.refl (Fin n) * τ = τ := by ext x; rfl
    simpa only [h₁, h₂] using FiniteBijection.blockEquiv_mul σ (Equiv.refl (Fin m))
      (Equiv.refl (Fin n)) τ
  rw [he, FiniteBijection.permutation_mul, CategoryTheory.Functor.map_comp,
    Category.assoc, nullaryPrefixDelete_prefix_invariant,
    nullaryPrefixDelete_tail_equivariance]

/-- 第二の色の係数への指定射影。 -/
def twoColorRightCoefficient (m n : ℕ) :
    (operad A).arity (m + n) ⟶ (operad A).arity n := nullaryPrefixDelete A m n

/-- 第一の色の係数への指定射影。 -/
def twoColorLeftCoefficient (m n : ℕ) :
    (operad A).arity (m + n) ⟶ (operad A).arity m :=
  (operad A).arityBijectionMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap m n) ≫ nullaryPrefixDelete A n m

/-- 第二の色への射影は、二色のブロック内置換を第二の色の置換へ移す。 -/
lemma twoColorRightCoefficient_equivariance (m n : ℕ)
    (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)) :
    (operad A).sequence.map
      (FiniteBijection.permutation (m + n) (FiniteBijection.blockEquiv σ τ)) ≫
        twoColorRightCoefficient A m n = twoColorRightCoefficient A m n ≫
          (operad A).sequence.map (FiniteBijection.permutation n τ) :=
  nullaryPrefixDelete_block_equivariance A m n σ τ

/-- 第一の色への射影は、二色のブロック内置換を第一の色の置換へ移す。 -/
lemma twoColorLeftCoefficient_equivariance (m n : ℕ)
    (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)) :
    (operad A).sequence.map
      (FiniteBijection.permutation (m + n) (FiniteBijection.blockEquiv σ τ)) ≫
        twoColorLeftCoefficient A m n = twoColorLeftCoefficient A m n ≫
          (operad A).sequence.map (FiniteBijection.permutation m σ) := by
  unfold twoColorLeftCoefficient
  rw [← Category.assoc, coefficientBlockSwap_naturality, Category.assoc,
    nullaryPrefixDelete_block_equivariance, ← Category.assoc]

/-- 二色部分群の元は、二つの指定射影の置換のブロック和である。 -/
lemma twoColorGroup_block (m n : ℕ) (g : TwoColorGroup.{u} m n) :
    g.val.down = FiniteBijection.blockEquiv (twoColorLeftProjection m n g).down
      (twoColorRightProjection m n g).down := by
  exact (congrArg (fun h : TwoColorGroup.{u} m n => h.val.down)
    ((twoColorGroupEquiv m n).apply_symm_apply g)).symm

end BarrattEccles
end SerrePositivity.EInfinity
