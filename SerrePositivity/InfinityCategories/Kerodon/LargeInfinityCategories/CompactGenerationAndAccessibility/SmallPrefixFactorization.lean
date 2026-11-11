module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.SmallSourceCosliceCompactness
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeMappingRestriction

/-!
概要：終対象を持たない小さい前置図式も固定して、全 compact 余錐を一段へ因子化する。
方針：前置 coslice の compact 判定と制限 left fibration の始対象因子化を使う。
規約：全小余極限は周囲の圏だけに要求する。
使われ方：長さ κ₀ の相対交互構成の極限前置段を前層内で保持する。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility


/-- 概要：小さい全前置図式を固定し、compact 図式の指定余錐を同じ表示脚へ因子化する。
方針：周囲の compact 余極限を取り、全前置 coslice での compact 性を使う。
規約：前置図式に終頂点を仮定せず、全制限と実際の比較辺を厳密に返す。
使われ方：極限段の前置図式全体を保つ相対一段延長。 -/
lemma compactDiagram_factorization_relative_smallPrefix
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {J L : SSet.{u}} [Quasicategory J] [Quasicategory L]
    (hJ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ J) (hL : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ L)
    {C : SSet.{u + 1}} [Quasicategory C] (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C)
    (q : (SSet.uliftFunctor.{u + 1, u}).obj J ⟶ C)
    (hQ : ∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (q.app _ j))
    (i : (SSet.uliftFunctor.{u + 1, u}).obj L ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj J) [Mono i]
    {A : SSet.{u}} [Quasicategory A] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered μ A]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (i ≫ q))
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
    (z : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q) (hz : z.restrict i = c.vertex) :
    ∃ j : A _⦋0⦌, ∃ w : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q,
      w.restrict i = D.app _ (ULift.up j) ∧
      ∃ k : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder q).Edge w z,
        (k.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict q i)).edge =
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg c (ULift.up j)).edge := by
  obtain ⟨cq, hcq⟩ := hC J q
  have hcompact := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_smallQuasicategoryColimit_universe hμ J hJ cq hcq hQ
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict q i
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceUnderRestrict_leftFibration_of_mono q i
  have hbase : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (p.app (Opposite.op ⦋0⦌) cq) := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.isKappaCompact_smallSourceCosliceVertex hμ hL hC (i ≫ q)
      (fun a ↦ hQ (i.app _ a)) (cq.restrict i)
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_restrict] using hcompact
  let zf : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p c.vertex) _⦋0⦌ :=
    ⟨z, by change p.app _ z = _; rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]; exact hz⟩
  obtain ⟨j, w, k, hk⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compactInitial_leftFibration_factorization
    p cq hcq hbase D c hc zf
  have hw : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.restrict (p := q) w.val i = D.app _ (ULift.up j) :=
    w.property.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero _)
  exact ⟨j, w.val, hw, k, hk⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility
