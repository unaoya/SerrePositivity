module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Functoriality.UniverseModuleFunctorFamily
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CochainModels.Cochains.CommonComplexUniverseComposition
/-!
概要：任意の対象宇宙の加群値 dg 関手の全区間族を、元の共通宇宙 Hom 入力上で評価する。
方針：共通宇宙変更の三角形則で実関手の Hom 作用へ戻し、同じ join prism を前合成する。
規約：Small は基準 dg 圏だけに置き、関手の始域には仮定しない。
使われ方：元左右 Hom 複体上の導来二作用を正本標的の作用と照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w e
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (E : Type e) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
lemma dgGluingModuleRawFunctorEvaluation (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R E (_root_.SerrePositivity.DifferentialGraded.RightModule R C)) (x y : E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedFamilyInterval.{u,v,max w e} R C
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u,max (u + 1) v} (F.map x y) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso (F.obj x) (F.obj y)).inv)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism
      ((SSet.uliftFunctor.{max (u + 1) v w e,max u v w e}).obj
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u,max u v w e} (homObject R E x y))) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommonComplexPinchedUniverseIso.{u,max u v w e,e,max (u + 1) v w e}
          (_root_.SerrePositivity.DifferentialGraded.homObject R E x y)).hom ≫
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniversePinchedComplexIso.{u,e,max (u + 1) v w e} R E x y).inv) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseNerveMap.{u,e,max (u + 1) v,max (u + 1) v w e} F ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedComparison.{u,v,max w e} R C := by
  let V := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommonComplexPinchedUniverseIso.{u,max u v w e,e,max (u + 1) v w e}
    (_root_.SerrePositivity.DifferentialGraded.homObject R E x y)).hom
  let G := (((SSet.uliftFunctor.{max (u + 1) v w e,max u e}).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u,e} (F.map x y)) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommonComplexPinchedUniverseIso.{u,e,max (u + 1) v,max (u + 1) v w e}
      (_root_.SerrePositivity.DifferentialGraded.homObject R (_root_.SerrePositivity.DifferentialGraded.RightModule R C) (F.obj x) (F.obj y))).hom ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniversePinchedComplexIso.{u,max (u + 1) v,max (u + 1) v w e}
      R (_root_.SerrePositivity.DifferentialGraded.RightModule R C) (F.obj x) (F.obj y)).inv) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedComparison.{u,v,max w e} R C)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (F.obj x))) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (F.obj y))) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _)
  have hg := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseFunctorIntervalImage.{u,e,max (u + 1) v,max (u + 1) v w e}
    F x y (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedComparison.{u,v,max w e} R C)
  have hv : V ≫ G = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedFamilyInterval.{u,v,max w e} R C
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u,max (u + 1) v} (F.map x y) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso (F.obj x) (F.obj y)).inv) := by
    dsimp only [V, G]
    simp only [Category.assoc]
    rw [reassoc_of% _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommonComplexUniverse_map_triangle.{u,max u v w e,e,max (u + 1) v,max (u + 1) v w e}
      (_root_.SerrePositivity.DifferentialGraded.homObject R E x y) (F.map x y)]
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleHomFamily.{u,v,max w e} R C (F.map x y)).symm
  rw [← hv, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, hg]
  rw [reassoc_of% _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism_naturality V,
    ← reassoc_of% _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry_precomp]
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
