module
public import SerrePositivity.InfinityCategories.Derived.Gluing.Category
public import SerrePositivity.InfinityCategories.Derived.PinchedComplexModelComparison
public import SerrePositivity.InfinityCategories.F1.UniversePinchedHom

/-! gluing の実写像空間を、同じ全 mapping cocone Hom 複体の空間模型へ移す。 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingHomMappingIso (X Y : DGGluingObject R C D M) :
    DGNerve.pinchedHom R (DGGluingObject R C D M) X Y ≅
      complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y) :=
  pinchedComplexModelIso X Y

def dgGluingUniverseHomMappingIso (X Y : DGGluingObject R C D M) :
    InfinityCategories.pinchedHom
        (X := (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
          (dgNerve R (DGGluingObject R C D M)))
        (ULift.up (Simplex.vertex X)) (ULift.up (Simplex.vertex Y)) ≅
      (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
        (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y)) :=
  (uliftPinchedHomIso.{max u v w, max (u + 1) v w}
    (C := dgNerve R (DGGluingObject R C D M)) (Simplex.vertex X) (Simplex.vertex Y)).symm ≪≫
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).mapIso
      (dgGluingHomMappingIso R C D M X Y)

end SerrePositivity.InfinityCategories
