module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeCoefficientCompositionPrisms
public import SerrePositivity.InfinityCategories.Derived.Gluing.PinchedFamilyCompositionPost
public import SerrePositivity.InfinityCategories.Derived.Gluing.CanonicalDerivedHomMap

/-! 元の augmentation 合成方程式を、β5 の実導来比較の同じ Hom 作用へ移す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]

def dgGluingModuleDerivedFamilyHom {K : SSet.{max (u + 1) v}} {P Q : RightModule R C}
    (f : K ⟶ DGNerve.pinchedHom R (RightModule R C) P Q) :=
  intervalFamilyHom ((f ≫ pinchedHomMap
    (dgModuleResolvedInfinity R (RightModule R C) C (DGFunctor.id (RightModule R C)))
    (DGNerve.Simplex.vertex P) (DGNerve.Simplex.vertex Q)) ≫
      pinchedHomToIntervalMappingSpace _ _)

variable (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingModuleDerivedLeftCoefficientFamily_comp (X Y : DGGluingObject R C D M) :
    dgGluingModuleDerivedFamilyHom R C (dgGluingNativeLeftCoefficientInput R C D M X Y) ≫
        dgGluingModuleDerivedFamilyHom R C
          (SSet.const (pinchedClosedVertex R (RightModule R C)
            (dgGluingAugmentation R C D M Y))) =
      dgGluingModuleDerivedFamilyHom R C
        (complexPinchedMap.{u, max (u + 1) v} (dgGluingLeftAction R C D M X Y) ≫
          (dgGluingCoefficientYonedaSpaceIso R C X.left (M.rightAt Y.right)).hom) := by
  exact dgGluingPinchedFamilyComposition_postcomp
    (dgModuleResolvedInfinity R (RightModule R C) C (DGFunctor.id (RightModule R C))) _ _ _
    (dgGluingNativeLeftCoefficientFamily_comp R C D M X Y)

lemma dgGluingModuleDerivedRightCoefficientFamily_comp (X Y : DGGluingObject R C D M) :
    dgGluingModuleDerivedFamilyHom R C
        (SSet.const (pinchedClosedVertex R (RightModule R C)
          (dgGluingAugmentation R C D M X))) ≫
        dgGluingModuleDerivedFamilyHom R C
          (dgGluingNativeRightCoefficientInput R C D M X Y) =
      dgGluingModuleDerivedFamilyHom R C
        (complexPinchedMap.{u, max (u + 1) v} (dgGluingRightAction R C D M X Y) ≫
          (dgGluingCoefficientYonedaSpaceIso R C X.left (M.rightAt Y.right)).hom) := by
  exact dgGluingPinchedFamilyComposition_postcomp
    (dgModuleResolvedInfinity R (RightModule R C) C (DGFunctor.id (RightModule R C))) _ _ _
    (dgGluingNativeRightCoefficientFamily_comp R C D M X Y)

end SerrePositivity.InfinityCategories
