module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleInputAugmentationSquare
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolvedAugmentationHomotopy
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLiftNervePrecomposition
/-!
概要：実入力 Up で制限した正方形の両円柱を、元の resolved augmentation の円柱へ同定する。
方針：同じ入力 Up の厳密等式と、全円柱の前合成自然性を使う。
規約：同じ実円柱射を保つ。使われ方：元の resolved precompIso の augmentation 正方形。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet MonoidalCategory
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (A C : Type (max (u + 1) v))
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R A] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (H : _root_.SerrePositivity.DifferentialGraded.DGFunctor R A C) (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
/-- 正方形の基底側の円柱は、元の resolved augmentation の入力 nerve による制限である。 -/
lemma dgModuleResolvedAugmentationHomotopy_precomp_inputBase_raw :
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedAugmentationHomotopy R C E F)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H)).h =
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationInputBaseHomotopy R C E F)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R A) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R A).comp
          (H.comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C))) ≫
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R C E F).inv)).h := by
  let S := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R C E F
  let UA := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R A)
  let UC := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C)
  let h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R A).comp
    (H.comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C)))
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H
  have hUp : UA ≫ h = q ≫ UC :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLift_sourcePrecomp_nerve.{u, v, v} R A C H
  have hm : q ≫ (UC ≫ S.inv) = UA ≫ h ≫ S.inv := by
    simpa only [Category.assoc] using congrArg (fun m => m ≫ S.inv) hUp.symm
  change (q ▷ (Δ[1] : SSet)) ≫ (((UC ≫ S.inv) ▷ (Δ[1] : SSet)) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationUnliftedHomotopy R C E F).h) =
      ((UA ≫ h ≫ S.inv) ▷ (Δ[1] : SSet)) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationUnliftedHomotopy R C E F).h
  simpa only [comp_whiskerRight, Category.assoc] using
    congrArg (fun m => (m ▷ (Δ[1] : SSet)) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationUnliftedHomotopy R C E F).h) hm
/-- 正方形の前合成側の円柱は、元の前合成関手の同じ resolved augmentation である。 -/
lemma dgModuleResolvedAugmentationHomotopy_precomp_source_raw :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedAugmentationHomotopy R A E (H.comp F)).h =
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationInputBaseHomotopy R C E F)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R A) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R A E (H.comp F)).inv ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompFunctor R A C E H F))).h := by
  let Q := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R A E (H.comp F)
  let UA := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R A)
  let J := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompFunctor R A C E H F)
  change ((UA ≫ Q.inv) ▷ (Δ[1] : SSet)) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationUnliftedHomotopy R A E (H.comp F)).h =
      ((UA ≫ Q.inv ≫ J) ▷ (Δ[1] : SSet)) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationUnliftedHomotopy R C E F).h
  simp only [comp_whiskerRight, Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationUnliftedHomotopy_precomp R A C E H F]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
