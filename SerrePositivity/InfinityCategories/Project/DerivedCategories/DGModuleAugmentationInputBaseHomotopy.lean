module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleAugmentationUnlifted
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolutionSourceDown
/-!
概要：同じ実 augmentation 円柱の終点を、持ち上げた実入力射影からの像で表す。
方針：実入力射影の下降の厳密等式だけで端点を輸送する。
規約：元の円柱射を保つ。使われ方：指定入力比較の厳密基底と augmentation の交換正方形。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
/-- 元の同じ終点は、持ち上げた入力射影・同じ下降・元の入力像の合成である。 -/
lemma dgModuleAugmentationTarget_inputBase :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationTarget R C E F) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceLift R C E F) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R C) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F := by
  have hp := congrArg (fun J => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map J ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceLift_comp_down R C E F)
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, Category.assoc] at hp
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationTarget, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp] using! hp.symm
/-- 端点だけを実入力射影の表示へ揃えた、元の同じ実 augmentation ホモトピー。 -/
def dgModuleAugmentationInputBaseHomotopy :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceLift R C E F) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R C) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) := by
  let A := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationUnliftedHomotopy R C E F
  exact { h := A.h
          h₀ := A.h₀
          h₁ := by
            simpa only [dgModuleAugmentationTarget_inputBase R C E F] using! A.h₁
          rel := A.rel }
end SerrePositivity.InfinityCategories.Project.DerivedCategories
