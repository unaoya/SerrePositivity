module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.BasisWeightSpan

/-!
# 基底を保つ同型による重み付き部分加群の移送

## 概要
Berger–Moerdijk §1 の自由表示を、同じ語で添字づけた基底の同型で移す。

## 方針
基底ベクトル上の式を線形写像の重み保存へ広げ、逆同型にも適用する。

## 規約
同型は加群の同型でよく、複体の微分との可換性は使わない。

## 使われ方
微分を消した自由代数から実際のセル段への重みの移送。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity
variable {A V W I : Type u} [CommRing A]
  [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W]

/-- An isomorphism identifying two indexed bases identifies their weight-bounded spans. -/
lemma mem_basisWeightSpan_iff_map (b : Module.Basis I A V) (c : Module.Basis I A W)
    (e : V ≃ₗ[A] W) (he : ∀ z, e (b z) = c z)
    (w : I → ℕ) (N : ℕ) (x : V) :
    x ∈ basisWeightSpan b w N ↔ e x ∈ basisWeightSpan c w N := by
  have h₁ : ∀ z, e (b z) ∈ basisWeightSpan c w (w z) := by
    intro z
    rw [he]
    exact basis_mem_basisWeightSpan c w z
  have h₂ : ∀ z, e.symm (c z) ∈ basisWeightSpan b w (w z) := by
    intro z
    rw [← he z, e.symm_apply_apply]
    exact basis_mem_basisWeightSpan b w z
  constructor
  · exact map_mem_basisWeightSpan b c w w e.toLinearMap h₁ N
  · intro hx
    have h := map_mem_basisWeightSpan c b w w e.symm.toLinearMap h₂ N hx
    simpa only [LinearEquiv.coe_coe, e.symm_apply_apply] using h

end SerrePositivity.EInfinity
