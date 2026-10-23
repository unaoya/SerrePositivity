module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseHomCoefficientPath
public import SerrePositivity.InfinityCategories.Derived.Gluing.CanonicalCoefficientMapping
public import SerrePositivity.InfinityCategories.Core.MappingSpaceRightKan
public import SerrePositivity.InfinityCategories.F1.Universe.InnerFibration

/-! canonical な導来 Hom 比較で、同じ実 gluing Hom の係数 path を移す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory
open DifferentialGraded
open HomotopyLimits SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingDerivedHomCoefficientActions (X Y : DGGluingObject R C D M) :=
  dgGluingUniverseHomCoefficientActions R C D M X Y ≫
    (dgGluingCanonicalCoefficientMappingComparison R C D M X.left Y.right ⊗ₘ
      dgGluingCanonicalCoefficientMappingComparison R C D M X.left Y.right)

def dgGluingDerivedHomCoefficientPathPullback (X Y : DGGluingObject R C D M) :=
  pullback (F2.arrowEndpointPair (InfinityCategories.pinchedHom
      (X := (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
        (dgModuleDerivedInfinityCategory R C))
      ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
        (ULift.up (DGNerve.Simplex.vertex X.left)))
      ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
        (ULift.up (DGNerve.Simplex.vertex Y.right)))))
    (dgGluingDerivedHomCoefficientActions R C D M X Y)

def dgGluingDerivedHomCoefficientPathComparison (X Y : DGGluingObject R C D M) :
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
      (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y)) ⟶
        dgGluingDerivedHomCoefficientPathPullback R C D M X Y :=
  dgGluingUniverseHomCoefficientPathComparison R C D M X Y ≫
    dgGluingKanPathPullbackTransport
      (dgGluingCanonicalCoefficientMappingComparison R C D M X.left Y.right)
      (dgGluingUniverseHomCoefficientActions R C D M X Y)

lemma dgGluingDerivedHomCoefficientPathComparison_equivalence
    (X Y : DGGluingObject R C D M) :
    IsSimplicialHomotopyEquivalence
      (dgGluingDerivedHomCoefficientPathComparison R C D M X Y) := by
  let : KanComplex
      (complexPinchedSpace.{u, max u v w} (homObject R C X.left Y.left) ⊗
        complexPinchedSpace.{u, max u v w} (homObject R D X.right Y.right)) :=
    F2.kanComplex_tensor _ _
  let : KanComplex (pullback
      (F2.arrowEndpointPair ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
        (complexPinchedSpace.{u, max u v w} (M.value X.left Y.right))))
      ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
          (complexPinchedMap.{u, max u v w} (dgGluingLeftAction R C D M X Y) ⊗ₘ
            complexPinchedMap.{u, max u v w} (dgGluingRightAction R C D M X Y)) ≫
        (uliftTensorIso _ _).hom)) :=
    dgGluingKanPathPullback_kanComplex _
  let : KanComplex (dgGluingDerivedHomCoefficientPathPullback R C D M X Y) :=
    dgGluingKanPathPullback_kanComplex _
  exact (dgGluingUniverseHomCoefficientPathComparison_equivalence R C D M X Y).comp
    (dgGluingKanPathPullbackTransport_equivalence _ _
      (dgGluingCanonicalCoefficientMappingComparison_equivalence R C D M X.left Y.right))

end SerrePositivity.InfinityCategories
