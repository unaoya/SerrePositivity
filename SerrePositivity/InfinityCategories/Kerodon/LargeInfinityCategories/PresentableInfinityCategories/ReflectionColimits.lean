module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.Definition
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.LocalReplacementReflection
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ReflectionSmallColimits

/-!
概要：既存の条件付き局所置換反射から局所対象圏の全小余極限を構成する。
方針：既存の反射を選び、周囲の余極限を同じ反射へ送る。
規約：局所置換の存在は入力とし、局所対象の accessibility はここでは仮定しない。
使われ方：局所対象の accessibility と合わせて presentability を得る。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 概要：局所対象の既存の反射と周囲の小余極限から内部の全小余極限を得る。
方針：同じ反射の余極限構成を適用する。
規約：元の全部分圏と元の任意小図式を使用する。
使われ方：条件付き presentability の余完備性。 -/
lemma hasSmallColimits_of_reflection {C : SSet.{u + 1}} [Quasicategory C]
    {I : Type u} (edges : I → C _⦋1⦌) (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C)
    (r : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsReflectiveSubcategory C (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject (Set.range edges))) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.Definition.Category edges) := by
  obtain ⟨r⟩ := r
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.reflectiveSubcategory_hasSmallColimits r hC

/-- 概要：各対象の既存の局所置換から局所対象圏の全小余極限が従う。
方針：N の条件付き反射を使い、周囲の余極限を反射する。
規約：元の局所同値と指定局所対象を入力にする。
使われ方：局所置換からの presentability の余完備性。 -/
lemma hasSmallColimits_of_localReplacements {C : SSet.{u + 1}} [Quasicategory C]
    {I : Type u} (edges : I → C _⦋1⦌) (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C)
    (hreplace : ∀ x : C _⦋0⦌, ∃ (y : C _⦋0⦌)
      (e : Truncated.Edge (X := (truncation 2).obj C) x y),
      e.edge ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.localEquivalences (Set.range edges) ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject (Set.range edges) y) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.Definition.Category edges) :=
  hasSmallColimits_of_reflection edges hC
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.isReflectiveSubcategory_of_localReplacements (Set.range edges) hreplace)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
