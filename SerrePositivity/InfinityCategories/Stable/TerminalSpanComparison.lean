module
public import SerrePositivity.InfinityCategories.Stable.TerminalArrowComparison
public import SerrePositivity.InfinityCategories.Core.PushoutHomotopy

/-! # 終対象へ向かう span との比較

概要：同じ始点を持つ span から、両端が終対象である span への単体的ホモトピーが存在する。
方針：二辺それぞれの始点固定の比較を、標準ホーンの pushout で貼り合わせる。
規約：終対象へ向かう二辺は指定したものを厳密に保つ。
使われ方：cofiber の入力図式から suspension の入力図式への辺。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：共通の始点を持つ span から終対象を両端とする span へのホモトピーが存在する。
方針：二つの比較ホモトピーの始点固定条件を用いて pushout で貼る。
規約：値域は quasicategory。使われ方：cofiber の span から suspension の span への比較。 -/
lemma exists_terminalSpanComparison {X : SSet.{u}} [Quasicategory X]
    {x y₁ y₂ z₁ z₂ : X _⦋0⦌}
    (f₁ : SSet.Truncated.Edge (X := (truncation 2).obj X) x y₁)
    (f₂ : SSet.Truncated.Edge (X := (truncation 2).obj X) x y₂)
    (g₁ : SSet.Truncated.Edge (X := (truncation 2).obj X) x z₁)
    (g₂ : SSet.Truncated.Edge (X := (truncation 2).obj X) x z₂)
    (hz₁ : IsTerminalVertex z₁) (hz₂ : IsTerminalVertex z₂) :
    ∃ H : SSet.Homotopy (edgeSpan f₁ f₂) (edgeSpan g₁ g₂),
      ((stdSimplex.δ (1 : Fin 2) ≫ horn₂₀.ι₀₁) ▷ (Δ[1] : SSet.{u})) ≫ H.h =
        CartesianMonoidalCategory.snd Δ[0] Δ[1] ≫ SSet.const x := by
  obtain ⟨L, hL⟩ := exists_terminalArrowComparison f₁ g₁ hz₁
  obtain ⟨R, hR⟩ := exists_terminalArrowComparison f₂ g₂ hz₂
  have P : IsPushout (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u}))
      (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u}))
      (horn₂₀.ι₀₁ ▷ (Δ[1] : SSet.{u})) (horn₂₀.ι₀₂ ▷ (Δ[1] : SSet.{u})) :=
    horn₂₀.isPushout.map (tensorRight (Δ[1] : SSet.{u}))
  have hw : (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ L.h =
      (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ R.h := hL.trans hR.symm
  refine ⟨{
    h := P.desc L.h R.h hw
    h₀ := ?_
    h₁ := ?_
    rel := ?_ }, ?_⟩
  · apply horn₂₀.isPushout.hom_ext
    · rw [← Category.assoc, ← SSet.ι₀_comp, Category.assoc, P.inl_desc, L.h₀]
      change SSet.yonedaEquiv.symm f₁.edge = horn₂₀.ι₀₁ ≫ edgeSpan f₁ f₂
      exact (edgeSpan_left f₁ f₂).symm
    · rw [← Category.assoc, ← SSet.ι₀_comp, Category.assoc, P.inr_desc, R.h₀]
      change SSet.yonedaEquiv.symm f₂.edge = horn₂₀.ι₀₂ ≫ edgeSpan f₁ f₂
      exact (edgeSpan_right f₁ f₂).symm
  · apply horn₂₀.isPushout.hom_ext
    · rw [← Category.assoc, ← SSet.ι₁_comp, Category.assoc, P.inl_desc, L.h₁]
      change SSet.yonedaEquiv.symm g₁.edge = horn₂₀.ι₀₁ ≫ edgeSpan g₁ g₂
      exact (edgeSpan_left g₁ g₂).symm
    · rw [← Category.assoc, ← SSet.ι₁_comp, Category.assoc, P.inr_desc, R.h₁]
      change SSet.yonedaEquiv.symm g₂.edge = horn₂₀.ι₀₂ ≫ edgeSpan g₁ g₂
      exact (edgeSpan_right g₁ g₂).symm
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property
  · change ((stdSimplex.δ (1 : Fin 2) ≫ horn₂₀.ι₀₁) ▷ (Δ[1] : SSet.{u})) ≫
      P.desc L.h R.h hw = _
    rw [comp_whiskerRight, Category.assoc, P.inl_desc]
    exact hL

end SerrePositivity.InfinityCategories
