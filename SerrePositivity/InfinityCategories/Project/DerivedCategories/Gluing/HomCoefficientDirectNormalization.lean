module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomCoefficientDirectCylinder
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomCoefficientCylinderNormalization

/-! 元の負 primitive の直接ホモトピーと主係数 path は、両作用を固定して比較できる。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory DifferentialGraded
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingHomCoefficientDirectHomotopy (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedHomotopy_of_cochain.{u, max u v w}
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M X Y ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction R C D M X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M X Y ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R C D M X Y)
    (-_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D M X Y) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomNegativePrimitive_boundary R C D M X Y)

lemma dgGluingHomCoefficientCylinderPrism_direct (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomCoefficientCylinderPrism R C D M X Y =
      (β_ (Δ[1] : SSet.{max u v w})
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max u v w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X Y))).hom ≫
        (dgGluingHomCoefficientDirectHomotopy R C D M X Y).h := by
  rw [dgGluingHomCoefficientDirectHomotopy, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedHomotopy_of_cochain_prism,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomCoefficientCylinderPrism, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomCoefficientCylinderExtension_direct]
  rfl

lemma dgGluingHomCoefficientDirectNormalization_exists (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    ∃ H : SSet.Homotopy
        ((β_ (Δ[1] : SSet.{max u v w})
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max u v w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X Y))).hom ≫
          (dgGluingHomCoefficientDirectHomotopy R C D M X Y).h)
        (uncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomCoefficientIntervalPath R C D M X Y)),
      (((SSet.boundary 1).ι ▷
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max u v w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X Y)) ▷
          (Δ[1] : SSet.{max u v w})) ≫ H.h =
        fst ((SSet.boundary 1 : SSet.{max u v w}) ⊗
            _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max u v w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X Y))
          (Δ[1] : SSet.{max u v w}) ≫
          ((SSet.boundary 1).ι ▷
            _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max u v w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X Y)) ≫
          uncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomCoefficientIntervalPath R C D M X Y) := by
  obtain ⟨H, hH⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomCoefficientCylinderNormalization_exists R C D M X Y
  refine ⟨_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget H
    (dgGluingHomCoefficientCylinderPrism_direct R C D M X Y) rfl, ?_⟩
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyRetarget_h]
  exact hH

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
