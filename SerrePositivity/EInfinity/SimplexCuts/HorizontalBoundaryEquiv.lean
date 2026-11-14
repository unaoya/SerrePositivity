module

public import SerrePositivity.EInfinity.SimplexCuts.BoundaryEndpointPartition
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Prod

/-!
# 水平な全境界と係数の文字削除の添字

Berger–Fresse §2.2.7、M14 L09a。
始点・内部・終点の既存の挿入同値を、係数の文字位置の三分割で貼り合わせる。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 一つだけの位置と既存の切断の積から、その切断を読む。 -/
def singletonSlotProdEquiv (X : Type*) : Fin 1 × X ≃ X where
  toFun := Prod.snd
  invFun x := (0, x)
  left_inv t := by
    apply Prod.ext
    · apply Fin.ext
      have h := t.1.isLt
      change 0 = t.1.val
      omega
    · rfl
  right_inv _ := rfl

/-- C70の証明分割：係数の文字位置を始点・内部・終点へ分ける。 -/
def firstInteriorLastIndexEquiv (m : ℕ) :
    Fin (m + 2) ≃ Fin 1 ⊕ (Fin m ⊕ Fin 1) :=
  (finCongr (by omega : m + 2 = 1 + (m + 1))).trans
    ((finSumFinEquiv : Fin 1 ⊕ Fin (m + 1) ≃ Fin (1 + (m + 1))).symm.trans
      (Equiv.sumCongr (Equiv.refl _) (finSumFinEquiv : Fin m ⊕ Fin 1 ≃ Fin (m + 1)).symm))

/-- C70：係数の添字の三つの位置と、小さい切断の積の貼り合わせ。 -/
def coefficientIndexEndpointEquiv (m q : ℕ) :
    Fin (m + 2) × Cut m q ≃ Cut m q ⊕ ((Cut m q × Fin m) ⊕ Cut m q) :=
  (Equiv.prodCongr (firstInteriorLastIndexEquiv m) (Equiv.refl _)).trans
    ((Equiv.sumProdDistrib _ _ _).trans
      (Equiv.sumCongr (singletonSlotProdEquiv _)
        ((Equiv.sumProdDistrib _ _ _).trans
          (Equiv.sumCongr (Equiv.prodComm _ _) (singletonSlotProdEquiv _)))))

/-- C71：係数の一文字削除と、全ての水平な出力境界の有限な同値。 -/
def horizontalBoundaryFaceEquiv (m q : ℕ) :
    Fin (m + 2) × Cut m q ≃ BoundaryVertexOfKind (m + 1) q .horizontal :=
  (coefficientIndexEndpointEquiv m q).trans
    ((Equiv.sumCongr (horizontalFirstFaceEquiv m q)
      (Equiv.sumCongr (horizontalInteriorFaceEquiv m q) (horizontalLastFaceEquiv m q))).trans
        (boundaryEndpointPartitionEquiv (m + 1) q .horizontal (by omega)).symm)

end SerrePositivity.EInfinity.SimplexCuts
