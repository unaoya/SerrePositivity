module

public import SerrePositivity.BhattScholze.Andre.DeltaDivisionCoefficientAut

/-!
# André E1・E2：raw δ 包の係数自己同型比較の合成

## 概要

係数 δ 自己同型を順に適用した raw 除算包の比較射は、合成自己同型の比較射と一致する。
BS Rem 7.15（著者版 p.62）の係数成分と指数成分の比較に使う。

## 方針

両射の δ 互換性を確かめ、係数と初期除算変数での外延性を適用する。

## 規約

入力族・分母の正則性や完備性は要求しない。

## 使われ方

係数 Frobenius と指数 p 倍を別々に作用させる raw 射を全体の射と比較する。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze.Andre
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 概要：raw 包の係数自己同型比較は自己同型の合成と両立する。
方針：係数合成の等式と初期変数の保存を使い、δ 射の外延性で証明する。
規約：e の後に f を適用する向き。
使われ方：BS Rem 7.15（著者版 p.62）の Frobenius 分解の raw 包への移送。 -/
theorem deltaDivisionCoefficientAutMap_trans
    (D : DeltaStructure p A) (e f : A ≃+* A)
    (he : D.IsDeltaHom D e.toRingHom) (hf : D.IsDeltaHom D f.toRingHom)
    (d : A) (a : σ → A) :
    (deltaDivisionCoefficientAutMap D f hf (e d) (fun s => e (a s))).comp
      (deltaDivisionCoefficientAutMap D e he d a) =
    deltaDivisionCoefficientAutMap D (e.trans f) (hf.comp he) d a := by
  have h₁ := deltaDivisionCoefficientAutMap_spec D e he d a
  have h₂ := deltaDivisionCoefficientAutMap_spec D f hf (e d) (fun s => e (a s))
  have h₃ := deltaDivisionCoefficientAutMap_spec D (e.trans f) (hf.comp he) d a
  apply deltaAdjoinDivisionHom_ext D
    (deltaAdjoinDivisionStructure D (f (e d)) (fun s => f (e (a s)))) d a
    _ _ (h₂.1.comp h₁.1) h₃.1
  · rw [RingHom.comp_assoc, h₁.2.1, ← RingHom.comp_assoc, h₂.2.1, h₃.2.1]
    rfl
  · intro s
    rw [RingHom.comp_apply, h₁.2.2, h₂.2.2]
    exact (h₃.2.2 s).symm

end SerrePositivity.BhattScholze.Andre
