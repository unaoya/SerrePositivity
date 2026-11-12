module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ComponentCompactPullback
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.SmallQuasicategoryColimitCompact
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.PullbackSmallColimits

/-!
概要：引き戻しの compact 成分条件は小さい quasicategory 上の余極限で閉じる。
方針：元の余錐を両射影で写し、実証済みの全極限錐族の自然比較による compact 閉性を使う。
規約：引き戻しの accessibility や一般の有限交換は仮定しない。
使われ方：compact な成分表示を同期する余極限操作。

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

/-- 概要：compact 成分の μ-small quasicategory 図式の元の余極限も compact 成分を持つ。
方針：同じ余錐の両成分へ小さい quasicategory 余極限の compact 閉性を適用する。
規約：元の引き戻しと指定余錐を保持し、射影の保存性だけを要求する。
使われ方：成分表示の同期に使う小さい連鎖の余極限。 -/
lemma componentCompactVertex_smallQuasicategoryColimit {μ : Cardinal.{u}}
    [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    (K : SSet.{u}) [Quasicategory K] (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ K)
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (p : E ⟶ B) (q : D ⟶ B) [InnerFibration p]
    (hf : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits (pullback.fst p q))
    (hs : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits (pullback.snd p q))
    {F : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ pullback p q}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
    (hF : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ComponentCompactVertex μ p q (F.app (Opposite.op ⦋0⦌) i)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ComponentCompactVertex μ p q c.vertex := by
  constructor
  · have hx := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_smallQuasicategoryColimit_universe hμ K hK
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (pullback.fst p q) c) (hf K F c hc)
      (fun i ↦ (hF i).1)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.mapJoinCocone_vertex] at hx
    exact hx
  · have hx := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_smallQuasicategoryColimit_universe hμ K hK
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (pullback.snd p q) c) (hs K F c hc)
      (fun i ↦ (hF i).2)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.mapJoinCocone_vertex] at hx
    exact hx

/-- 概要：余極限保存 cospan の引き戻しでは compact 成分の小さい quasicategory 余極限も compact 成分を持つ。
方針：元の cospan の保存性から両射影の保存を構成し、同じ余錐へ閉性を適用する。
規約：同値持ち上げと余完備性は元の成分にのみ要求する。
使われ方：presentable cospan の filtered 生成表示の同期。 -/
lemma componentCompactVertex_smallQuasicategoryColimit_of_span {μ : Cardinal.{u}}
    [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    (K : SSet.{u}) [Quasicategory K] (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ K)
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (p : E ⟶ B) (q : D ⟶ B) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p)
    (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits E) (hD : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits D)
    (hpc : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits p) (hqc : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits q)
    {F : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ pullback p q}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
    (hF : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ComponentCompactVertex μ p q (F.app (Opposite.op ⦋0⦌) i)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ComponentCompactVertex μ p q c.vertex := by
  have : InnerFibration p := hp.innerFibration
  exact componentCompactVertex_smallQuasicategoryColimit hμ K hK p q
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.pullback_fst_preservesSmallColimits p q hp hE hD hpc hqc)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.pullback_snd_preservesSmallColimits p q hp hE hD hpc hqc) c hc hF

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
