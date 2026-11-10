module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.ArrowCardinals
public import SerrePositivity.InfinityCategories.F2.Presentable.PresentableSpanCompactCardinals

/-!
概要：周囲で compact な全候補射の両端点も compact となる共通濃度を構成する。
方針：公開された compact 保存濃度の構成を、射圏の二つの評価関手に適用する。
規約：生成射だけの端点条件と、全 compact 射の端点条件を混同しない。
使われ方：HTT 5.5.4.13–14 の compact 端点を持つ部分表示の同時細分。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
variable {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

/-- 全 compact 候補の両端点を compact に保ち、全生成射を含む共通正則濃度がある。 -/
lemma exists_endpointCompactArrowCardinal (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C)
    (edges : I → C _⦋1⦌) (σ : Cardinal.{u}) :
    ∃ κ μ : Cardinal.{u}, κ.IsRegular ∧ μ.IsRegular ∧ σ < μ ∧
      IsCardinalChangeBound κ μ ∧ IsKappaAccessible μ C ∧
      IsKappaAccessible μ ((ihom (Δ[1] : SSet.{u + 1})).obj C) ∧
      (∀ i, Compact.IsKappaCompact.{u, u + 1} μ (generatorArrowVertex edges i)) ∧
      ∀ f : ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌,
        Compact.IsKappaCompact.{u, u + 1} μ f → ∀ j : Fin 2,
          Compact.IsKappaCompact.{u, u + 1} μ
            ((evaluateFunctorAt (stdSimplex.obj₀Equiv.symm j)).app _ f) := by
  obtain ⟨ρ, _, hσρ, hgen⟩ :=
    (arrow_isPresentable hC).isAccessible.exists_common_compactCardinal
      (generatorArrowVertex edges) σ
  let p : (ihom (Δ[1] : SSet.{u + 1})).obj C ⟶ C :=
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0)
  let q : (ihom (Δ[1] : SSet.{u + 1})).obj C ⟶ C :=
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1)
  obtain ⟨κ, μ, hκ, hμ, hρμ, hb, hAr, _, hCμ, hp, hq⟩ :=
    exists_presentableSpan_compactCardinal (arrow_isPresentable hC) (arrow_isPresentable hC)
      hC p q (evaluateFunctorAt_preservesSmallColimits hC.hasSmallColimits _)
      (evaluateFunctorAt_preservesSmallColimits hC.hasSmallColimits _) ρ
  refine ⟨κ, μ, hκ, hμ, hσρ.trans hρμ, hb, hCμ, hAr,
    fun i ↦ (hgen i).of_le hρμ.le, ?_⟩
  intro f hf j
  fin_cases j
  · exact hp f hf
  · exact hq f hf

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
