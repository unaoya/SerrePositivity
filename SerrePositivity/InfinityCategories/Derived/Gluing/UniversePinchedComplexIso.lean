module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseFunctorHomModelComparison

/-! 一般宇宙の実 pinched Hom と同じ Hom 複体模型の標準同型。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v r
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial

def dgGluingUniversePinchedComplexIso (R : Type u) [CommRing R]
    (C : Type v) [DGCategory R C] (x y : C) :
    InfinityCategories.pinchedHom
        (X := (SSet.uliftFunctor.{r, max u v}).obj (dgNerve R C))
        (ULift.up (Simplex.vertex x)) (ULift.up (Simplex.vertex y)) ≅
      (SSet.uliftFunctor.{r, max u v}).obj
        (complexPinchedSpace.{u, v} (homObject R C x y)) :=
  (uliftPinchedHomIso.{max u v, r}
    (C := dgNerve R C) (Simplex.vertex x) (Simplex.vertex y)).symm ≪≫
    (SSet.uliftFunctor.{r, max u v}).mapIso (pinchedComplexModelIso x y)

end SerrePositivity.InfinityCategories
