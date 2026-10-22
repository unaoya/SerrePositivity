module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CoefficientPathEquivalence
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomotopyIsoPrecomposition
public import SerrePositivity.InfinityCategories.HomotopyLimits.KanEquivalencePaths

/-! 同じ係数 path 比較を通常の区間関手空間へ移し、その同値性と全区間族を保つ。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded
open scoped Simplicial
variable {R : Type u} [CommRing R] (Q : Complex R)

def dgGluingCoefficientIntervalPathComparison :
    complexPinchedSpace.{u, v} (dgGluingComplexPath Q) ⟶
      (ihom (Δ[1] : SSet.{max u v})).obj (complexPinchedSpace.{u, v} Q) :=
  dgGluingCoefficientPathComparison Q ≫ equivalencePathι _

lemma dgGluingCoefficientIntervalPathComparison_equivalence :
    IsSimplicialHomotopyEquivalence (dgGluingCoefficientIntervalPathComparison.{u, v} Q) :=
  (dgGluingHomotopyEquivalence_postcomp_iso_iff _
    (asIso (equivalencePathι (complexPinchedSpace.{u, v} Q)))).mpr
      (dgGluingCoefficientPathComparison_equivalence Q)

lemma dgGluingCoefficientIntervalPathComparison_start :
    dgGluingCoefficientIntervalPathComparison.{u, v} Q ≫
        evaluateFunctorAt (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      complexPinchedMap.{u, v} (dgGluingComplexPathStart Q) := by
  rw [dgGluingCoefficientIntervalPathComparison, Category.assoc,
    ← equivalencePathEndpoint]
  exact dgGluingCoefficientPathComparison_start Q

lemma dgGluingCoefficientIntervalPathComparison_end :
    dgGluingCoefficientIntervalPathComparison.{u, v} Q ≫
        evaluateFunctorAt (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      complexPinchedMap.{u, v} (dgGluingComplexPathEnd Q) := by
  rw [dgGluingCoefficientIntervalPathComparison, Category.assoc,
    ← equivalencePathEndpoint]
  exact dgGluingCoefficientPathComparison_end Q

lemma dgGluingCoefficientIntervalPathComparison_uncurry :
    uncurry (dgGluingCoefficientIntervalPathComparison.{u, v} Q) =
      (β_ (Δ[1] : SSet.{max u v})
        (complexPinchedSpace.{u, v} (dgGluingComplexPath Q))).hom ≫
          (dgGluingComplexPathSpaceHomotopy.{u, v} Q).h := by
  rw [dgGluingCoefficientIntervalPathComparison, dgGluingCoefficientPathComparison_family,
    uncurry_curry]

end SerrePositivity.InfinityCategories
