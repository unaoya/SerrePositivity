module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomDerivedCoefficientCompositionLifts
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomDerivedCoefficientDiagonalBoundary
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.IntervalUncurryHomotopyInverse
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomotopyIntervalPath
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomotopyRetargetValue

/-! 同じ実係数 path を、主比較と同じ二合成対応の対角間の全区間族へ移す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory DifferentialGraded
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingHomDerivedLastCompositionDiagonal (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedLastComposition R C D M X Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceDiagonal
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X.left))) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedAugmentationEdge R C D M Y)

def dgGluingHomDerivedFirstCompositionDiagonal (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedFirstComposition R C D M X Y ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionDiagonal (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedAugmentationEdge R C D M X)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y.right)))

def dgGluingHomDerivedCompositionUncurriedHomotopy (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    SSet.Homotopy
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (dgGluingHomDerivedLastCompositionDiagonal R C D M X Y))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (dgGluingHomDerivedFirstCompositionDiagonal R C D M X Y)) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedCoefficientDiagonalHomotopy R C D M X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedLastComposition_diagonal R C D M X Y).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedFirstComposition_diagonal R C D M X Y).symm

lemma dgGluingHomDerivedCompositionUncurriedHomotopy_h (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (dgGluingHomDerivedCompositionUncurriedHomotopy R C D M X Y).h =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedCoefficientDiagonalHomotopy R C D M X Y).h := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyRetarget_h
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedCoefficientDiagonalHomotopy R C D M X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedLastComposition_diagonal R C D M X Y).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedFirstComposition_diagonal R C D M X Y).symm

lemma dgGluingHomDerivedCompositionUncurriedHomotopy_source (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ▷ (Δ[1] : SSet.{max (u + 1) v w})) ≫
        (dgGluingHomDerivedCompositionUncurriedHomotopy R C D M X Y).h =
      SSet.const ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X.left))) := by
  rw [dgGluingHomDerivedCompositionUncurriedHomotopy_h R C D M X Y]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedCoefficientDiagonalHomotopy_source R C D M X Y

lemma dgGluingHomDerivedCompositionUncurriedHomotopy_target (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ▷ (Δ[1] : SSet.{max (u + 1) v w})) ≫
        (dgGluingHomDerivedCompositionUncurriedHomotopy R C D M X Y).h =
      SSet.const ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y.right))) := by
  rw [dgGluingHomDerivedCompositionUncurriedHomotopy_h R C D M X Y]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedCoefficientDiagonalHomotopy_target R C D M X Y

def dgGluingHomDerivedCompositionDiagonalHomotopy (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    SSet.Homotopy (dgGluingHomDerivedLastCompositionDiagonal R C D M X Y)
      (dgGluingHomDerivedFirstCompositionDiagonal R C D M X Y) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIntervalUncurryHomotopyInverse
    (dgGluingHomDerivedCompositionUncurriedHomotopy R C D M X Y)
    (dgGluingHomDerivedCompositionUncurriedHomotopy_source R C D M X Y)
    (dgGluingHomDerivedCompositionUncurriedHomotopy_target R C D M X Y)

lemma dgGluingHomDerivedCompositionDiagonalHomotopy_evaluate
    (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (α_ (Δ[1] : SSet.{max (u + 1) v w})
        ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max u v w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X Y)))
        (Δ[1] : SSet.{max (u + 1) v w})).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (dgGluingHomDerivedCompositionDiagonalHomotopy R C D M X Y).h =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedCoefficientDiagonalHomotopy R C D M X Y).h :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIntervalUncurryHomotopyInverseMap_evaluate
    (dgGluingHomDerivedCompositionUncurriedHomotopy R C D M X Y)
    (dgGluingHomDerivedCompositionUncurriedHomotopy_source R C D M X Y)
    (dgGluingHomDerivedCompositionUncurriedHomotopy_target R C D M X Y)).trans
      (dgGluingHomDerivedCompositionUncurriedHomotopy_h R C D M X Y)

def dgGluingHomDerivedCompositionDiagonalPath (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyIntervalPath (dgGluingHomDerivedCompositionDiagonalHomotopy R C D M X Y)

lemma dgGluingHomDerivedCompositionDiagonalPath_start (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    dgGluingHomDerivedCompositionDiagonalPath R C D M X Y ≫
        (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 0).app _ =
      dgGluingHomDerivedLastCompositionDiagonal R C D M X Y :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyIntervalPath_start _

lemma dgGluingHomDerivedCompositionDiagonalPath_end (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    dgGluingHomDerivedCompositionDiagonalPath R C D M X Y ≫
        (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 1).app _ =
      dgGluingHomDerivedFirstCompositionDiagonal R C D M X Y :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyIntervalPath_end _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
