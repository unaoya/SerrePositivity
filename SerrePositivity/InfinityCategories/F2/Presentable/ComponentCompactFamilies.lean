module

public import SerrePositivity.InfinityCategories.F2.Presentable.RealizedPullbackCandidates
public import SerrePositivity.InfinityCategories.F2.Presentable.SmallCompactFamilies
public import SerrePositivity.InfinityCategories.F2.Presentable.ComponentCompactPullback

/-!
概要：両成分が compact な引き戻し頂点の全てを小さい族で代表する。
方針：両成分の compact 代表族と、実現される基底同型の符号族を組み合わせる。
規約：元の圏の固定頂点写像の小ささと、指定同型を保つ新しい持ち上げ供給を要求しない。
使われ方：引き戻しの filtered 生成圏に使う小さい compact 対象族。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：compact 成分の全部分圏の全対象は小さい一族で代表される。
方針：両成分の小さい compact 代表を選び、同じ基底符号の二実現を比較する。
規約：引き戻しの accessibility を仮定しない。
使われ方：compact 生成候補の対象集合の小ささ。 -/
lemma exists_smallComponentCompactFamily {μ : Cardinal.{u}}
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (hE : IsKappaAccessible μ E) (hD : IsKappaAccessible μ D) (hB : IsLocallySmall B)
    (p : E ⟶ B) (q : D ⟶ B) [InnerFibration p] :
    ∃ (T : Type u) (v : T → (pullback p q) _⦋0⦌),
      (∀ t, ComponentCompactVertex μ p q (v t)) ∧
      ∀ x, ComponentCompactVertex μ p q x → ∃ t, Nonempty (VertexIso x (v t)) := by
  obtain ⟨AE, vE, hvE, he⟩ := hE.exists_smallCompactFamily
  obtain ⟨AD, vD, hvD, hd⟩ := hD.exists_smallCompactFamily
  refine ⟨RealizedPullbackCandidateIndex p q hB vE vD,
    realizedPullbackCandidateVertex p q hB vE vD,
    realizedPullbackCandidate_components_compact p q hB vE vD hvE hvD, ?_⟩
  intro x hx
  obtain ⟨a, ⟨e⟩⟩ := he _ hx.1
  obtain ⟨b, ⟨d⟩⟩ := hd _ hx.2
  exact exists_realizedPullbackCandidate_iso p q hB vE vD x a b e d

/-- 概要：compact 成分を全て代表する小さい族を、引き戻し内でも native compact に選べる。
方針：成分代表族の被覆と構成済みの実引き戻しの compact 判定を組み合わせる。
規約：両射影と第一の辺の filtered 保存、第一の辺の compact 保存を明示する。
使われ方：元の引き戻しの小さい compact 生成候補。 -/
lemma exists_smallNativeCompactPullbackFamily {κ μ : Cardinal.{u}}
    [Fact κ.IsRegular] [Fact μ.IsRegular] (h : IsCardinalChangeBound κ μ)
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (hE : IsKappaAccessible μ E) (hD : IsKappaAccessible μ D) (hB : IsLocallySmall B)
    (p : E ⟶ B) (q : D ⟶ B) [InnerFibration p]
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ (pullback.fst p q))
    (hs : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ (pullback.snd p q))
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ p)
    (hpCompact : ∀ x, Compact.IsKappaCompact.{u, u + 1} μ x →
      Compact.IsKappaCompact.{u, u + 1} μ (p.app _ x)) :
    ∃ (T : Type u) (v : T → (pullback p q) _⦋0⦌),
      (∀ t, Compact.IsKappaCompact.{u, u + 1} μ (v t)) ∧
      (∀ t, ComponentCompactVertex μ p q (v t)) ∧
      ∀ x, ComponentCompactVertex μ p q x → ∃ t, Nonempty (VertexIso x (v t)) := by
  obtain ⟨T, v, hv, hc⟩ := exists_smallComponentCompactFamily hE hD hB p q
  refine ⟨T, v, ?_, hv, hc⟩
  intro t
  exact isKappaCompact_pullback_of_components h p q hf hs hp (v t)
    (hv t).1 (hv t).2 (hpCompact _ (hv t).1)

end SerrePositivity.InfinityCategories.F2.Presentable
