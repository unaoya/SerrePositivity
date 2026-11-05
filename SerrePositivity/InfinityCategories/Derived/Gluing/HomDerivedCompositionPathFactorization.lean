module
public import SerrePositivity.InfinityCategories.Derived.Gluing.DerivedCoefficientIntervalMap
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomDerivedCompositionDiagonalPath
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomotopyIntervalPathPostcomp

/-! 入力付き二合成対角間の全 path は、保存済みの係数全 path の同じ区間 Hom 像。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingHomDerivedCompositionDiagonalHomotopy_factor
    (X Y : DGGluingObject R C D M) :
    (dgGluingHomDerivedCompositionDiagonalHomotopy R C D M X Y).h =
      (functorHomotopyPostcomp
        (dgGluingIntervalPathHomotopy (dgGluingDerivedHomCoefficientIntervalPath R C D M X Y))
        (dgGluingDerivedCoefficientIntervalMap R C D M X.left Y.right)).h := by
  apply intervalMappingUncurry_injective _ _
  apply (cancel_epi (α_ (Δ[1] : SSet.{max (u + 1) v w})
    ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
      (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y)))
    (Δ[1] : SSet.{max (u + 1) v w})).hom).mp
  rw [dgGluingHomDerivedCompositionDiagonalHomotopy_evaluate R C D M X Y]
  change _ ≫ intervalMappingUncurry
      ((dgGluingIntervalPathHomotopy
        (dgGluingDerivedHomCoefficientIntervalPath R C D M X Y)).h ≫
        (dgGluingDerivedCoefficientEndpointIso R C D M X.left Y.right).inv ≫
          pinchedHomToIntervalMappingSpace _ _) = _
  exact congrArg (fun k => _ ≫ k)
    (dgGluingDerivedCoefficientIntervalMap_uncurry R C D M X.left Y.right
      (dgGluingIntervalPathHomotopy
        (dgGluingDerivedHomCoefficientIntervalPath R C D M X Y)).h).symm

lemma dgGluingHomDerivedCompositionDiagonalPath_factor (X Y : DGGluingObject R C D M) :
    dgGluingHomDerivedCompositionDiagonalPath R C D M X Y =
      dgGluingDerivedHomCoefficientIntervalPath R C D M X Y ≫
        (ihom (Δ[1] : SSet.{max (u + 1) v w})).map
          (dgGluingDerivedCoefficientIntervalMap R C D M X.left Y.right) := by
  change curry (_ ≫ (dgGluingHomDerivedCompositionDiagonalHomotopy R C D M X Y).h) = _
  rw [dgGluingHomDerivedCompositionDiagonalHomotopy_factor R C D M X Y]
  exact dgGluingHomotopyIntervalPath_postcomp _ _

end SerrePositivity.InfinityCategories
