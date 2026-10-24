module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeDerivedCoefficientComposition
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorCompositionTriangle
public import SerrePositivity.InfinityCategories.Derived.Gluing.DGCompositionFunctorTriangle

/-! native 合成 prism から直接作り、導来比較の同じ実三辺を保持する合成三角形。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]

def dgGluingModuleDerivedFamilyHomotopy {K : SSet.{max (u + 1) v}} {P Q : RightModule R C}
    (f : K ⟶ DGNerve.pinchedHom R (RightModule R C) P Q) :=
  intervalFamilyHomotopy ((f ≫ pinchedHomMap
    (dgModuleResolvedInfinity R (RightModule R C) C (DGFunctor.id (RightModule R C)))
    (DGNerve.Simplex.vertex P) (DGNerve.Simplex.vertex Q)) ≫
      pinchedHomToIntervalMappingSpace _ _)

variable (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingModuleDerivedLeftCoefficientTriangle_nonempty (X Y : DGGluingObject R C D M) :
    Nonempty (FunctorCompositionTriangle
      (dgGluingModuleDerivedFamilyHomotopy R C (dgGluingNativeLeftCoefficientInput R C D M X Y))
      (dgGluingModuleDerivedFamilyHomotopy R C
        (SSet.const (pinchedClosedVertex R (RightModule R C) (dgGluingAugmentation R C D M Y))))
      (dgGluingModuleDerivedFamilyHomotopy R C
        (complexPinchedMap.{u, max (u + 1) v} (dgGluingLeftAction R C D M X Y) ≫
          (dgGluingCoefficientYonedaSpaceIso R C X.left (M.rightAt Y.right)).hom))) := by
  apply nonempty_functorCompositionTriangle_of_homEq
  exact dgGluingModuleDerivedLeftCoefficientFamily_comp R C D M X Y

lemma dgGluingModuleDerivedRightCoefficientTriangle_nonempty (X Y : DGGluingObject R C D M) :
    Nonempty (FunctorCompositionTriangle
      (dgGluingModuleDerivedFamilyHomotopy R C
        (SSet.const (pinchedClosedVertex R (RightModule R C) (dgGluingAugmentation R C D M X))))
      (dgGluingModuleDerivedFamilyHomotopy R C (dgGluingNativeRightCoefficientInput R C D M X Y))
      (dgGluingModuleDerivedFamilyHomotopy R C
        (complexPinchedMap.{u, max (u + 1) v} (dgGluingRightAction R C D M X Y) ≫
          (dgGluingCoefficientYonedaSpaceIso R C X.left (M.rightAt Y.right)).hom))) := by
  apply nonempty_functorCompositionTriangle_of_homEq
  exact dgGluingModuleDerivedRightCoefficientFamily_comp R C D M X Y

def dgGluingModuleDerivedLeftCoefficientTriangle (X Y : DGGluingObject R C D M) :=
  Eq.mp
    (congrArg (fun f => FunctorCompositionTriangle
      (dgGluingModuleDerivedFamilyHomotopy R C (dgGluingNativeLeftCoefficientInput R C D M X Y))
      (dgGluingModuleDerivedFamilyHomotopy R C
        (SSet.const (pinchedClosedVertex R (RightModule R C) (dgGluingAugmentation R C D M Y))))
      (dgGluingModuleDerivedFamilyHomotopy R C f))
      (dgGluingNativeLeftCoefficientComposition R C D M X Y))
    (dgGluingDGCompositionFunctorTriangle R (RightModule R C)
      (dgGluingNativeLeftCoefficientInput R C D M X Y)
      (SSet.const (pinchedClosedVertex R (RightModule R C) (dgGluingAugmentation R C D M Y)))
      (dgModuleResolvedInfinity R (RightModule R C) C (DGFunctor.id (RightModule R C))))

def dgGluingModuleDerivedRightCoefficientTriangle (X Y : DGGluingObject R C D M) :=
  Eq.mp
    (congrArg (fun f => FunctorCompositionTriangle
      (dgGluingModuleDerivedFamilyHomotopy R C
        (SSet.const (pinchedClosedVertex R (RightModule R C) (dgGluingAugmentation R C D M X))))
      (dgGluingModuleDerivedFamilyHomotopy R C (dgGluingNativeRightCoefficientInput R C D M X Y))
      (dgGluingModuleDerivedFamilyHomotopy R C f))
      (dgGluingNativeRightCoefficientComposition R C D M X Y))
    (dgGluingDGCompositionFunctorTriangle R (RightModule R C)
      (SSet.const (pinchedClosedVertex R (RightModule R C) (dgGluingAugmentation R C D M X)))
      (dgGluingNativeRightCoefficientInput R C D M X Y)
      (dgModuleResolvedInfinity R (RightModule R C) C (DGFunctor.id (RightModule R C))))

end SerrePositivity.InfinityCategories
