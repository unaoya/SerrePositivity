module

public import SerrePositivity.InfinityCategories.F2.Presentable.SmallPullbackModels
public import SerrePositivity.InfinityCategories.F2.Presentable.SmallCompactModels
public import SerrePositivity.InfinityCategories.F2.Presentable.ComponentCompactPullback

/-!
概要：一般の accessible 成分を持つ引き戻しの compact 成分圏に、小さい全同値模型を与える。
方針：全 compact 制限 cospan の三成分模型を選び、実引き戻しの小さい模型と同一視する。
規約：元の圏の固定頂点写像の小ささと引き戻しの accessibility は要求しない。
使われ方：presentable 引き戻しの小さい compact 生成圏。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：全 compact 制限を持つ一般の cospan の compact 成分圏は小さい ∞ 圏と全同値。
方針：三つの全 compact 圏の小さい模型から制限 cospan の実引き戻しを縮小する。
規約：元の両成分が厳密に小さいとは仮定せず、全 compact の元の辺と高次を保持する。
使われ方：引き戻しの filtered 生成表示を小さい生成圏へまとめる。 -/
lemma exists_smallComponentCompactModel {μ : Cardinal.{u}}
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (hE : IsKappaAccessible μ E) (hD : IsKappaAccessible μ D) (hB : IsKappaAccessible μ B)
    (p : E ⟶ B) (q : D ⟶ B) (hp : F1B.EquivalenceLifting p)
    (hpCompact : ∀ x, Compact.IsKappaCompact.{u, u + 1} μ x →
      Compact.IsKappaCompact.{u, u + 1} μ (p.app _ x))
    (hqCompact : ∀ x, Compact.IsKappaCompact.{u, u + 1} μ x →
      Compact.IsKappaCompact.{u, u + 1} μ (q.app _ x)) :
    letI := hp.innerFibration
    ∃ (A : SSet.{u}) (hA : Quasicategory A),
      letI := hA
      Nonempty (QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj A)
        (componentCompactObjects μ p q)) := by
  have : InnerFibration p := hp.innerFibration
  obtain ⟨AE, hAE, ⟨e⟩⟩ := hE.exists_smallCompactModel
  obtain ⟨AD, hAD, ⟨d⟩⟩ := hD.exists_smallCompactModel
  obtain ⟨AB, hAB, ⟨b⟩⟩ := hB.exists_smallCompactModel
  have := hAE
  have := hAD
  have := hAB
  have hpr : F1B.EquivalenceLifting (kappaCompactRestriction μ p hpCompact) :=
    kappaCompactRestriction_equivalenceLifting μ p hpCompact hp
  have : InnerFibration (kappaCompactRestriction μ p hpCompact) := hpr.innerFibration
  obtain ⟨A, hA, ⟨a⟩⟩ := exists_smallStrictPullbackModel_of_component_models e d b
    (kappaCompactRestriction μ p hpCompact) (kappaCompactRestriction μ q hqCompact)
    hpr
  have := hA
  exact ⟨A, hA, ⟨a.trans (qCatEquivalenceOfIso
    (componentCompactObjects_isPullback μ p q hpCompact hqCompact).isoPullback.symm)⟩⟩

end SerrePositivity.InfinityCategories.F2.Presentable
