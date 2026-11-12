module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PullbackCoconeCandidates

/-!
概要：元の二つの全余錐値が厳密に一致するとき、そのまま実引き戻しの余錐にする。
方針：元の全余錐射を実際の引き戻しへ持ち上げる。
規約：quasicategory 性や同値持ち上げは追加しない。
使われ方：compact 成分射影の under comma の全余錐の最後の貼り合わせ。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

/-- 概要：元の実引き戻し図式の二成分余錐が厳密に整合すれば元の図式に余錐がある。
方針：同じ二つの全余錐値を引き戻しへ貼り、固定入力を両射影で検出する。
規約：全入力を厳密に保ち、充填性は要求しない。
使われ方：指定始点の下の compact comma の全試験余錐。 -/
def strictPullbackCocone {E D B K : SSet.{u}} (p : E ⟶ B) (q : D ⟶ B)
    (r : K ⟶ pullback p q)
    (cE : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (r ≫ pullback.fst p q))
    (cD : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (r ≫ pullback.snd p q))
    (h : cE.val ≫ p = cD.val ≫ q) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone r := by
  refine ⟨pullback.lift cE.val cD.val h, ?_⟩
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst]
    exact cE.property
  · rw [Category.assoc, pullback.lift_snd]
    exact cD.property

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility
