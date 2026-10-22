module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomCoefficientDirectCylinder
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomCoefficientCylinderNormalization

/-! 元の負 primitive の直接ホモトピーと主係数 path は、両作用を固定して比較できる。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory DifferentialGraded
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingHomCoefficientDirectHomotopy (X Y : DGGluingObject R C D M) :=
  dgGluingComplexPinchedHomotopy_of_cochain.{u, max u v w}
    (dgGluingLeftHomMap R C D M X Y ≫ dgGluingLeftAction R C D M X Y)
    (dgGluingRightHomMap R C D M X Y ≫ dgGluingRightAction R C D M X Y)
    (-dgGluingHomPrimitive R C D M X Y) (dgGluingHomNegativePrimitive_boundary R C D M X Y)

lemma dgGluingHomCoefficientCylinderPrism_direct (X Y : DGGluingObject R C D M) :
    dgGluingHomCoefficientCylinderPrism R C D M X Y =
      (β_ (Δ[1] : SSet.{max u v w})
        (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y))).hom ≫
        (dgGluingHomCoefficientDirectHomotopy R C D M X Y).h := by
  rw [dgGluingHomCoefficientDirectHomotopy, dgGluingComplexPinchedHomotopy_of_cochain_prism,
    dgGluingHomCoefficientCylinderPrism, dgGluingHomCoefficientCylinderExtension_direct]
  rfl

lemma dgGluingHomCoefficientDirectNormalization_exists (X Y : DGGluingObject R C D M) :
    ∃ H : SSet.Homotopy
        ((β_ (Δ[1] : SSet.{max u v w})
          (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y))).hom ≫
          (dgGluingHomCoefficientDirectHomotopy R C D M X Y).h)
        (uncurry (dgGluingHomCoefficientIntervalPath R C D M X Y)),
      (((SSet.boundary 1).ι ▷
          complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y)) ▷
          (Δ[1] : SSet.{max u v w})) ≫ H.h =
        fst ((SSet.boundary 1 : SSet.{max u v w}) ⊗
            complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y))
          (Δ[1] : SSet.{max u v w}) ≫
          ((SSet.boundary 1).ι ▷
            complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y)) ≫
          uncurry (dgGluingHomCoefficientIntervalPath R C D M X Y) := by
  obtain ⟨H, hH⟩ := dgGluingHomCoefficientCylinderNormalization_exists R C D M X Y
  refine ⟨stableHomotopyRetarget H
    (dgGluingHomCoefficientCylinderPrism_direct R C D M X Y) rfl, ?_⟩
  rw [dgGluingHomotopyRetarget_h]
  exact hH

end SerrePositivity.InfinityCategories
