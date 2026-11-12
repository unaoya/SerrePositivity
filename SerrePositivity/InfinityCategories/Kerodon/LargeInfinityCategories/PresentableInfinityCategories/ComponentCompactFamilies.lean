module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RealizedPullbackCandidates
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallCompactFamilies
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ComponentCompactPullback

/-!
概要：両成分が compact な引き戻し頂点の全てを小さい族で代表する。
方針：両成分の compact 代表族と、実現される基底同型の符号族を組み合わせる。
規約：元の圏の固定頂点写像の小ささと、指定同型を保つ新しい持ち上げ供給を要求しない。
使われ方：引き戻しの filtered 生成圏に使う小さい compact 対象族。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：compact 成分の全部分圏の全対象は小さい一族で代表される。
方針：両成分の小さい compact 代表を選び、同じ基底符号の二実現を比較する。
規約：引き戻しの accessibility を仮定しない。
使われ方：compact 生成候補の対象集合の小ささ。 -/
lemma exists_smallComponentCompactFamily {μ : Cardinal.{u}}
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ E) (hD : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ D) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsLocallySmall B)
    (p : E ⟶ B) (q : D ⟶ B) [InnerFibration p] :
    ∃ (T : Type u) (v : T → (pullback p q) _⦋0⦌),
      (∀ t, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ComponentCompactVertex μ p q (v t)) ∧
      ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ComponentCompactVertex μ p q x → ∃ t, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x (v t)) := by
  obtain ⟨AE, vE, hvE, he⟩ := hE.exists_smallCompactFamily
  obtain ⟨AD, vD, hvD, hd⟩ := hD.exists_smallCompactFamily
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RealizedPullbackCandidateIndex p q hB vE vD,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.realizedPullbackCandidateVertex p q hB vE vD,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.realizedPullbackCandidate_components_compact p q hB vE vD hvE hvD, ?_⟩
  intro x hx
  obtain ⟨a, ⟨e⟩⟩ := he _ hx.1
  obtain ⟨b, ⟨d⟩⟩ := hd _ hx.2
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_realizedPullbackCandidate_iso p q hB vE vD x a b e d

/-- 概要：compact 成分を全て代表する小さい族を、引き戻し内でも native compact に選べる。
方針：成分代表族の被覆と構成済みの実引き戻しの compact 判定を組み合わせる。
規約：両射影と第一の辺の filtered 保存、第一の辺の compact 保存を明示する。
使われ方：元の引き戻しの小さい compact 生成候補。 -/
lemma exists_smallNativeCompactPullbackFamily {κ μ : Cardinal.{u}}
    [Fact κ.IsRegular] [Fact μ.IsRegular] (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ)
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ E) (hD : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ D) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsLocallySmall B)
    (p : E ⟶ B) (q : D ⟶ B) [InnerFibration p]
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ (pullback.fst p q))
    (hs : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ (pullback.snd p q))
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ p)
    (hpCompact : ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ x →
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (p.app _ x)) :
    ∃ (T : Type u) (v : T → (pullback p q) _⦋0⦌),
      (∀ t, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (v t)) ∧
      (∀ t, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ComponentCompactVertex μ p q (v t)) ∧
      ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ComponentCompactVertex μ p q x → ∃ t, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x (v t)) := by
  obtain ⟨T, v, hv, hc⟩ := exists_smallComponentCompactFamily hE hD hB p q
  refine ⟨T, v, ?_, hv, hc⟩
  intro t
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isKappaCompact_pullback_of_components h p q hf hs hp (v t)
    (hv t).1 (hv t).2 (hpCompact _ (hv t).1)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
