module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseNerveMap
public import SerrePositivity.InfinityCategories.Derived.Gluing.Projections

/-! 異なる対象宇宙の元の gluing 圏と二脚を、同じ単体宇宙に配置する。 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingUniverseLeftNerve :
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
      (dgNerve R (DGGluingObject R C D M)) ⟶
    (SSet.uliftFunctor.{max (u + 1) v w, max u v}).obj (dgNerve R C) :=
  dgGluingUniverseNerveMap.{u, max u v w, v, max (u + 1) v w}
    (dgGluingLeft R C D M)

def dgGluingUniverseRightNerve :
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
      (dgNerve R (DGGluingObject R C D M)) ⟶
    (SSet.uliftFunctor.{max (u + 1) v w, max u w}).obj (dgNerve R D) :=
  dgGluingUniverseNerveMap.{u, max u v w, w, max (u + 1) v w}
    (dgGluingRight R C D M)

def dgGluingUniverseYoneda :
    (SSet.uliftFunctor.{max (u + 1) v w, max u v}).obj (dgNerve R C) ⟶
    (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
      (dgNerve R (RightModule R C)) :=
  dgGluingUniverseNerveMap.{u, v, max (u + 1) v, max (u + 1) v w} (dgYoneda R C)

def dgGluingUniverseCoefficient :
    (SSet.uliftFunctor.{max (u + 1) v w, max u w}).obj (dgNerve R D) ⟶
    (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
      (dgNerve R (RightModule R C)) :=
  dgGluingUniverseNerveMap.{u, w, max (u + 1) v, max (u + 1) v w} M.toFunctor

end SerrePositivity.InfinityCategories
