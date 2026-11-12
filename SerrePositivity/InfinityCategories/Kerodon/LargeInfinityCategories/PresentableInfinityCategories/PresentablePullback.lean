module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.PullbackSmallColimits

/-!
概要：accessible 引き戻しの一般命題から presentable 引き戻しを得る。
方針：一般命題へ両脚の accessibility を渡し、既存の小余極限構成と合わせる。
規約：一般命題は明示入力とし、P-d 所有の構成を import・複製しない。
使われ方：一般版の到着時にその証明を代入する e5 の接続。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：accessible 引き戻し一般版を入力とする presentable 引き戻し。
方針：余極限保存から両脚の accessibility を得て、引き戻しの余完備性と組み合わせる。
規約：入力は任意の accessible 三対象・両脚に対する一般命題全体。
使われ方：P-d の一般版を代入して無条件の公開入口を得る。 -/
lemma pullback_isPresentable_of_accessiblePullback
    (hAccessible : ∀ {E D B : SSet.{u + 1}}
      [Quasicategory E] [Quasicategory D] [Quasicategory B]
      (p : E ⟶ B) (q : D ⟶ B) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible E → _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible D → _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible B →
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessibleFunctor p → _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessibleFunctor q →
      letI := hp.innerFibration
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible (pullback p q))
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (p : E ⟶ B) (q : D ⟶ B) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p)
    (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) (hD : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable D) (hB : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable B)
    (hpc : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits p) (hqc : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits q) :
    letI := hp.innerFibration
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (pullback p q) := by
  have := hp.innerFibration
  exact ⟨hAccessible p q hp hE.isAccessible hD.isAccessible hB.isAccessible
    hpc.isAccessibleFunctor hqc.isAccessibleFunctor,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.pullback_hasSmallColimits p q hp hE.hasSmallColimits hD.hasSmallColimits hpc hqc⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
