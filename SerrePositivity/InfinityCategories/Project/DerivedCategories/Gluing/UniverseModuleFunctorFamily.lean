module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UniverseFunctorIntervalImage
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UniverseModuleDerivedFamilies
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UniverseDerivedStructure

/-! 加群値 dg 関手の実 Hom 作用を、同じ Hom 鎖写像から作った導来全区間族へ同定する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]

lemma dgGluingUniverseModuleHomFamily {K : _root_.SerrePositivity.DifferentialGraded.Complex R} {P Q : _root_.SerrePositivity.DifferentialGraded.RightModule R C}
    (φ : K ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R (_root_.SerrePositivity.DifferentialGraded.RightModule R C) P Q) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedFamilyInterval.{u, v, w} R C
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} φ ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso P Q).inv) =
      ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v w} φ) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommonComplexPinchedUniverseIso.{u, max u v w,
          max (u + 1) v, max (u + 1) v w}
          (_root_.SerrePositivity.DifferentialGraded.homObject R (_root_.SerrePositivity.DifferentialGraded.RightModule R C) P Q)).hom) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniversePinchedComplexIso.{u, max (u + 1) v, max (u + 1) v w}
          R (_root_.SerrePositivity.DifferentialGraded.RightModule R C) P Q).inv ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedComparison.{u, v, w} R C)
          (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex P)) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Q)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _ := by
  have hu := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedUniverseIso_naturality.{u, max u v w, max (u + 1) v}
    φ
  change (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v w} φ) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommonComplexPinchedUniverseIso.{u, max u v w,
        max (u + 1) v, max (u + 1) v w} _).hom = _ at hu
  rw [hu]
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniversePinchedComplexIso, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedComparison]
  have hn := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.uliftPinchedHomIso_naturality.{max (u + 1) v, max (u + 1) v w}
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R C) C (DGFunctor.id (RightModule R C)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex P) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Q)
  rw [Category.assoc, Category.assoc, ← reassoc_of% hn]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedFamilyInterval, Functor.map_comp, Category.assoc]
  rfl

variable (E : Type (max u v w)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]

lemma dgGluingUniverseModuleFunctorFamily (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R E (_root_.SerrePositivity.DifferentialGraded.RightModule R C)) (x y : E) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedFamilyInterval.{u, v, w} R C
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} (F.map x y) ≫
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso (F.obj x) (F.obj y)).inv) =
      ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v w} (F.map x y)) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommonComplexPinchedUniverseIso.{u, max u v w,
          max (u + 1) v, max (u + 1) v w}
          (_root_.SerrePositivity.DifferentialGraded.homObject R (_root_.SerrePositivity.DifferentialGraded.RightModule R C) (F.obj x) (F.obj y))).hom) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniversePinchedComplexIso.{u, max (u + 1) v, max (u + 1) v w}
          R (_root_.SerrePositivity.DifferentialGraded.RightModule R C) (F.obj x) (F.obj y)).inv ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedComparison.{u, v, w} R C)
          (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (F.obj x))) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (F.obj y))) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _ :=
  dgGluingUniverseModuleHomFamily R C (F.map x y)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
