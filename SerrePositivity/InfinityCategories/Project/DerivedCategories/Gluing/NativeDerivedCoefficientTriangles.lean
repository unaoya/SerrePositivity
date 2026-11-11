module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.NativeDerivedCoefficientComposition
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGCompositionFunctorTriangle

/-! native 合成 prism から直接作り、導来比較の同じ実三辺を保持する合成三角形。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory DifferentialGraded
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]

def dgGluingModuleDerivedFamilyHomotopy {K : SSet.{max (u + 1) v}} {P Q : RightModule R C}
    (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R (RightModule R C) P Q) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy ((f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R C) C (DGFunctor.id (RightModule R C)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex P) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Q)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _)

variable (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingModuleDerivedLeftCoefficientTriangle_nonempty (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle
      (dgGluingModuleDerivedFamilyHomotopy R C (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeLeftCoefficientInput R C D M X Y))
      (dgGluingModuleDerivedFamilyHomotopy R C
        (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex R (RightModule R C) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M Y))))
      (dgGluingModuleDerivedFamilyHomotopy R C
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction R C D M X Y) ≫
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoefficientYonedaSpaceIso R C X.left (M.rightAt Y.right)).hom))) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.nonempty_functorCompositionTriangle_of_homEq
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModuleDerivedLeftCoefficientFamily_comp R C D M X Y

lemma dgGluingModuleDerivedRightCoefficientTriangle_nonempty (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle
      (dgGluingModuleDerivedFamilyHomotopy R C
        (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex R (RightModule R C) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M X))))
      (dgGluingModuleDerivedFamilyHomotopy R C (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeRightCoefficientInput R C D M X Y))
      (dgGluingModuleDerivedFamilyHomotopy R C
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R C D M X Y) ≫
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoefficientYonedaSpaceIso R C X.left (M.rightAt Y.right)).hom))) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.nonempty_functorCompositionTriangle_of_homEq
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModuleDerivedRightCoefficientFamily_comp R C D M X Y

def dgGluingModuleDerivedLeftCoefficientTriangle (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :=
  Eq.mp
    (congrArg (fun f => _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle
      (dgGluingModuleDerivedFamilyHomotopy R C (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeLeftCoefficientInput R C D M X Y))
      (dgGluingModuleDerivedFamilyHomotopy R C
        (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex R (RightModule R C) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M Y))))
      (dgGluingModuleDerivedFamilyHomotopy R C f))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeLeftCoefficientComposition R C D M X Y))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDGCompositionFunctorTriangle R (RightModule R C)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeLeftCoefficientInput R C D M X Y)
      (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex R (RightModule R C) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M Y)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R C) C (DGFunctor.id (RightModule R C))))

def dgGluingModuleDerivedRightCoefficientTriangle (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :=
  Eq.mp
    (congrArg (fun f => _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle
      (dgGluingModuleDerivedFamilyHomotopy R C
        (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex R (RightModule R C) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M X))))
      (dgGluingModuleDerivedFamilyHomotopy R C (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeRightCoefficientInput R C D M X Y))
      (dgGluingModuleDerivedFamilyHomotopy R C f))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeRightCoefficientComposition R C D M X Y))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDGCompositionFunctorTriangle R (RightModule R C)
      (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex R (RightModule R C) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M X)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeRightCoefficientInput R C D M X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R C) C (DGFunctor.id (RightModule R C))))

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
