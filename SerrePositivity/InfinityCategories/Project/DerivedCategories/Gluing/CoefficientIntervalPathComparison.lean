module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CoefficientPathEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomotopyIsoPrecomposition
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.KanEquivalencePaths

/-! 同じ係数 path 比較を通常の区間関手空間へ移し、その同値性と全区間族を保つ。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] (Q : Complex R)

def dgGluingCoefficientIntervalPathComparison :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPath Q) ⟶
      (ihom (Δ[1] : SSet.{max u v})).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, v} Q) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoefficientPathComparison Q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι _

lemma dgGluingCoefficientIntervalPathComparison_equivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (dgGluingCoefficientIntervalPathComparison.{u, v} Q) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyEquivalence_postcomp_iso_iff _
    (asIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, v} Q)))).mpr
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoefficientPathComparison_equivalence Q)

lemma dgGluingCoefficientIntervalPathComparison_start :
    dgGluingCoefficientIntervalPathComparison.{u, v} Q ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathStart Q) := by
  rw [dgGluingCoefficientIntervalPathComparison, Category.assoc,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoefficientPathComparison_start Q

lemma dgGluingCoefficientIntervalPathComparison_end :
    dgGluingCoefficientIntervalPathComparison.{u, v} Q ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathEnd Q) := by
  rw [dgGluingCoefficientIntervalPathComparison, Category.assoc,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoefficientPathComparison_end Q

lemma dgGluingCoefficientIntervalPathComparison_uncurry :
    uncurry (dgGluingCoefficientIntervalPathComparison.{u, v} Q) =
      (β_ (Δ[1] : SSet.{max u v})
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPath Q))).hom ≫
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathSpaceHomotopy.{u, v} Q).h := by
  rw [dgGluingCoefficientIntervalPathComparison, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoefficientPathComparison_family,
    uncurry_curry]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
