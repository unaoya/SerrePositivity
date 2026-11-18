module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SlotPermutations
public import Mathlib.Algebra.Group.ULift

/-!
# 二色の入力の置換部分群

## 概要
HA 3.2.4.7 の自由代数の比較に使う Σ_m × Σ_n の埋め込みを固定する。

## 方針
既存の `FiniteBijection.blockEquiv` を群準同型にし、両ブロックでの評価で単射性を示す。

## 規約
群の宇宙を arity の表現と同じ `ULift` にそろえる。左の m 入力、右の n 入力の順序。

## 使われ方
二色の係数解像度を同じ部分群へ制限し、同変な比較を構成する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.BarrattEccles

/-- HA 3.2.4.7 の二色の入力の置換を、連結した入力の置換へ埋め込む。 -/
def twoColorPermutationHom (m n : ℕ) :
    ULift.{u} (Equiv.Perm (Fin m) × Equiv.Perm (Fin n)) →*
      ULift.{u} (Equiv.Perm (Fin (m + n))) where
  toFun σ := ULift.up (FiniteBijection.blockEquiv σ.down.1 σ.down.2)
  map_one' := congrArg ULift.up (FiniteBijection.blockEquiv_refl m n)
  map_mul' σ τ := congrArg ULift.up
    (FiniteBijection.blockEquiv_mul σ.down.1 τ.down.1 σ.down.2 τ.down.2)

/-- 二色の埋め込みは各ブロックへの制限で検出でき、単射である（HA 3.2.4.7）。 -/
lemma twoColorPermutationHom_injective (m n : ℕ) :
    Function.Injective (twoColorPermutationHom.{u} m n) := by
  intro σ τ h
  apply ULift.ext
  apply Prod.ext
  · apply Equiv.ext
    intro i
    have hi := congrArg (fun k => k.down (i.castAdd n)) h
    change FiniteBijection.blockEquiv σ.down.1 σ.down.2 (i.castAdd n) =
      FiniteBijection.blockEquiv τ.down.1 τ.down.2 (i.castAdd n) at hi
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_apply_left, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_apply_left] at hi
    apply Fin.ext
    exact congrArg (fun z : Fin (m + n) => z.val) hi
  · apply Equiv.ext
    intro i
    have hi := congrArg (fun k => k.down (i.natAdd m)) h
    change FiniteBijection.blockEquiv σ.down.1 σ.down.2 (i.natAdd m) =
      FiniteBijection.blockEquiv τ.down.1 τ.down.2 (i.natAdd m) at hi
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_apply_right, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_apply_right] at hi
    apply Fin.ext
    exact Nat.add_left_cancel (congrArg (fun z : Fin (m + n) => z.val) hi)

end SerrePositivity.EInfinity.BarrattEccles
