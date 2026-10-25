module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.CompactCoconeFactorization
public import SerrePositivity.InfinityCategories.F2.Presentable.TerminalSourceCoslice
public import SerrePositivity.InfinityCategories.Stable.CoconeMappingRestriction

/-!
概要：終頂点を持つ既存の全前置図式を固定し、小さい compact 図式の全余錐を一段へ因子化する。
方針：公開 P の前置 coslice の compact 判定を、制限 left fibration の始対象へ適用する。
規約：指定した前置余錐を厳密に保ち、指定 filtered 余錐脚を被覆する実辺を返す。
使われ方：HTT 5.5.4.13 の coherent 交互構成の相対一段延長。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits

/-- compact な全余極限を持つ図式の余錐は、既存の終前置図式を固定して一段へ因子化する。 -/
lemma compactCocone_factorization_relative_terminalPrefix
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {K L C : SSet.{u + 1}} [Quasicategory L] [Quasicategory C]
    (q : K ⟶ C) (i : L ⟶ K) [Mono i] (t : L _⦋0⦌) (ht : IsTerminalVertex t)
    (cq : JoinCocone q) (hcq : IsColimitCone cq)
    (hpt : Compact.IsKappaCompact.{u, u + 1} μ ((i ≫ q).app _ t))
    (hcompact : Compact.IsKappaCompact.{u, u + 1} μ cq.vertex)
    {A : SSet.{u}} [Quasicategory A] [IsKappaFiltered μ A]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ sliceUnder (i ≫ q))
    (c : JoinCocone D) (hc : IsColimitCone c)
    (z : JoinCocone q) (hz : z.restrict i = c.vertex) :
    ∃ j : A _⦋0⦌, ∃ w : JoinCocone q,
      w.restrict i = D.app _ (ULift.up j) ∧
      ∃ k : (sliceUnder q).Edge w z,
        (k.map (sliceUnderRestrict q i)).edge = (Compact.coconeTransportLeg c (ULift.up j)).edge := by
  let p := sliceUnderRestrict q i
  have : LeftFibration p := sliceUnderRestrict_leftFibration_of_mono q i
  have hbase : Compact.IsKappaCompact.{u, u + 1} μ (p.app _ cq) := by
    change Compact.IsKappaCompact.{u, u + 1} μ (C := sliceUnder (i ≫ q)) (cq.restrict i)
    apply isKappaCompact_terminalSourceCosliceVertex hμ t ht (i ≫ q) (cq.restrict i) hpt
    simpa only [JoinCocone.vertex_restrict] using hcompact
  let zf : (vertexFiber p c.vertex) _⦋0⦌ :=
    ⟨z, by change p.app _ z = _; rw [pinchedConstant_zero]; exact hz⟩
  obtain ⟨j, w, k, hk⟩ := compactInitial_leftFibration_factorization p cq hcq hbase D c hc zf
  have hw : JoinCocone.restrict (p := q) w.val i = D.app _ (ULift.up j) := by
    change p.app _ w.val = _
    exact w.property.trans (pinchedConstant_zero _)
  exact ⟨j, w.val, hw, k, hk⟩

/-- 小さい compact 全図式には、同じ終前置図式を固定する相対一段因子化が存在する。 -/
lemma compactDiagram_factorization_relative_terminalPrefix
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {K : SSet.{u}} [Quasicategory K] (hK : IsKappaSmall μ K)
    {L C : SSet.{u + 1}} [Quasicategory L] [Quasicategory C]
    (hC : HasSmallColimits C) (q : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C)
    (hQ : ∀ k, Compact.IsKappaCompact.{u, u + 1} μ (q.app _ k))
    (i : L ⟶ (SSet.uliftFunctor.{u + 1, u}).obj K) [Mono i]
    (t : L _⦋0⦌) (ht : IsTerminalVertex t)
    {A : SSet.{u}} [Quasicategory A] [IsKappaFiltered μ A]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ sliceUnder (i ≫ q))
    (c : JoinCocone D) (hc : IsColimitCone c)
    (z : JoinCocone q) (hz : z.restrict i = c.vertex) :
    ∃ j : A _⦋0⦌, ∃ w : JoinCocone q,
      w.restrict i = D.app _ (ULift.up j) ∧
      ∃ k : (sliceUnder q).Edge w z,
        (k.map (sliceUnderRestrict q i)).edge = (Compact.coconeTransportLeg c (ULift.up j)).edge := by
  obtain ⟨cq, hcq⟩ := hC K q
  exact compactCocone_factorization_relative_terminalPrefix hμ q i t ht cq hcq
    (hQ (i.app _ t))
    (isKappaCompact_smallQuasicategoryColimit_universe hμ K hK cq hcq hQ) D c hc z hz

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
