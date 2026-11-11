module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.FiniteCoproductSiftedPreservation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SigmaSmallColimits

/-!
概要：P_Σ 上の全小余極限保存を有限余積と sifted 保存で判定する。
方針：反映からの小余積存在を一般保存判定へ渡す。
規約：Yoneda 制限上だけの有限余積保存への縮約は別工程。
使われ方：P_Σ の有限余積普遍性を証明するための一般判定。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 概要：P_Σ 上の全余極限保存は有限余積保存と sifted 保存に同値。
方針：構成した小余積存在を一般の bar 保存判定へ適用する。
規約：有限余積保存は元の関手全体の条件である。
使われ方：Yoneda 制限上の有限余積条件への縮約の最終段階。 -/
lemma sigma_preservesSmallColimits_iff_finiteCoproducts_sifted
    {C : SSet.{u}} [Quasicategory C] {D : SSet.{u + 1}} [Quasicategory D]
    (hC : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ C.op), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit p)
    (G : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits G ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesFiniteCoproducts G ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesSmallSiftedColimits G :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.preservesSmallColimits_iff_finiteCoproducts_sifted (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigma_hasSmallCoproducts hC) G

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
