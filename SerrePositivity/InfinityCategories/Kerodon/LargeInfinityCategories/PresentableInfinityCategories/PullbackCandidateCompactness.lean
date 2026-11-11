module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PullbackCompactObjects
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PullbackCandidateCardinals
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.PullbackSmallColimits

/-!
概要：presentable 圏の余極限保存関手の引き戻しの小さい候補族を、同じ濃度で compact にする。
方針：両成分と標的像の共通濃度を取り、元の射影の保存性と全 Hom の引き戻し判定を使う。
規約：引き戻し自身の accessibility や生成性を仮定しない。
使われ方：引き戻しの小さい compact 生成圏の候補を供給する。

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

/-- 概要：小さい候補族の全対象を、元の引き戻し内で同じ正則濃度の compact 対象にする。
方針：小さい成分族と像の濃度を揃え、全小余極限を保つ射影で全 Hom の保存へ接続する。
規約：候補が引き戻しを生成するという結論はこの定理に含めない。
使われ方：元の引き戻しの小さい compact 全部分候補模型。 -/
lemma exists_pullbackCandidate_nativeCompactCardinal
    {κ : Cardinal.{u}} [Fact κ.IsRegular]
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (p : E ⟶ B) (q : D ⟶ B) [InnerFibration p] (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p)
    (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) (hD : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable D) (hB : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable B)
    (hpc : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits p) (hqc : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits q)
    {AE AD : Type u} (vE : AE → E _⦋0⦌) (vD : AD → D _⦋0⦌) :
    ∃ μ : Cardinal.{u}, μ.IsRegular ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ ∧
      ∀ t : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PullbackCandidateIndex p q hB.isLocallySmall vE vD,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullbackCandidateFamily p q hB.isLocallySmall vE vD hp t) := by
  obtain ⟨μ, hμ, hb, hc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_pullbackCandidate_compactCardinal
    p q hp hE.isAccessible hD.isAccessible hB.isAccessible vE vD κ
  have : Fact μ.IsRegular := ⟨hμ⟩
  have hf := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.pullback_fst_preservesSmallColimits p q hp
    hE.hasSmallColimits hD.hasSmallColimits hpc hqc
  have hs := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.pullback_snd_preservesSmallColimits p q hp
    hE.hasSmallColimits hD.hasSmallColimits hpc hqc
  refine ⟨μ, hμ, hb, fun t ↦ ?_⟩
  obtain ⟨he, hd, hbase⟩ := hc t
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isKappaCompact_pullback_of_components hb p q
    (hf.isKappaAccessibleFunctor μ) (hs.isKappaAccessibleFunctor μ)
    (hpc.isKappaAccessibleFunctor μ) _ he hd hbase

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
