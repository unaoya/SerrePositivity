module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.SimplexShapeFamilyPushout

/-!
概要：任意の底の pushout を単体圏の nerve の pushout へ写す。
方針：各次数の射列を作用素の列と初単体の依存和に直し、係数の pushout を使う。
規約：境界を貼る射に単射性を仮定しない。
使われ方：一般のセル付加に対する反転関手の貼り合わせ。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 任意の底の pushout は、実際の単体圏の nerve でも pushout となる。 -/
lemma transportSimplexNerve_isPushout {A B C D : SSet.{u}}
    {i : A ⟶ B} {g : A ⟶ C} {k : B ⟶ D} {j : C ⟶ D} (h : IsPushout i g k j) :
    IsPushout (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor i)) (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor g))
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor k)) (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor j)) := by
  apply IsPushout.of_forall_isPushout_app
  rintro ⟨⟨n⟩⟩
  have hs := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplexShapeFamily_isPushout
    (fun τ : ComposableArrows SimplexCategoryᵒᵖ n ↦ h.app (τ.obj 0))
  apply hs.of_iso' (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexChainEquiv A n).toIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexChainEquiv B n).toIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexChainEquiv C n).toIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexChainEquiv D n).toIso
  all_goals rfl

/-- 任意の底の pushout では、指定辺を反転する関手の制限が実際の pullback をなす。 -/
lemma transportSimplexInverting_isPullback_of_isPushout {A B C D : SSet.{u}}
    {i : A ⟶ B} {g : A ⟶ C} {k : B ⟶ D} {j : C ⟶ D}
    (h : IsPushout i g k j) (E : SSet.{u}) :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInvertingRestriction j E)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInvertingRestriction k E)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInvertingRestriction g E)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInvertingRestriction i E) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInverting_isPullback_of_nerve_isPushout (transportSimplexNerve_isPushout h) E

/-- 底の単射は、実際の単体圏の nerve でも単射となる。 -/
instance transportSimplexNerveMap_mono {B D : SSet.{u}} (f : B ⟶ D) [Mono f] :
    Mono (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor f)) := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨⟨n⟩⟩
  rw [mono_iff_injective]
  intro σ τ h
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexChainEquiv B n).injective
  have he := congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexChainEquiv D n) h
  change (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplexShapeFamilyMap
    (fun s : ComposableArrows SimplexCategoryᵒᵖ n ↦ f.app (s.obj 0)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexChainEquiv B n σ) =
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplexShapeFamilyMap
      (fun s : ComposableArrows SimplexCategoryᵒᵖ n ↦ f.app (s.obj 0)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexChainEquiv B n τ) at he
  exact (mono_iff_injective (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplexShapeFamilyMap
    (fun s : ComposableArrows SimplexCategoryᵒᵖ n ↦ f.app (s.obj 0)))).mp inferInstance he

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
