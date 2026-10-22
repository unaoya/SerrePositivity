module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CoefficientPathComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.TwoEndpointPathSpace
public import SerrePositivity.InfinityCategories.Core.EquivalenceCalculus

/-! 同じ係数 path の比較は、元の始点への同値を厳密に回収するため実ホモトピー同値。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded
variable {R : Type u} [CommRing R] (Q : Complex R)

lemma dgGluingCoefficientPathComparison_equivalence :
    IsSimplicialHomotopyEquivalence (dgGluingCoefficientPathComparison.{u, v} Q) := by
  have he := isQCatEquivalence_of_trivialKanFibration
    (equivalencePathEndpoint (complexPinchedSpace.{u, v} Q) 0)
  have hc : IsQCatEquivalence (dgGluingCoefficientPathComparison.{u, v} Q ≫
      equivalencePathEndpoint (complexPinchedSpace.{u, v} Q) 0) := by
    rw [dgGluingCoefficientPathComparison_start]
    let : QuasiIso (dgGluingComplexPathStart Q) := dgGluingComplexPathStart_quasiIso Q
    exact (complexPinchedMap_quasiIso_equivalence _).isQCatEquivalence
  exact (he.cancel_right hc).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories
