module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneGammaUnitPoint
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.SimplexCounitContraction
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedSimplexCochainAugmentationZero

/-!
# Γ の指定単位の零次数の係数

DAG XIII §2.2 の基本円の照合への前段。指定単位の元を、同じ DK の余単位、
smart 切断の包含、単位複体の零次数の標準同型で読み、一であることを確かめる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded _root_.SerrePositivity.ComplexLimits
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- Γ の指定 AW 単位の係数は、同じ零次数の比較の下で一である。 -/
lemma gammaUnitSimplex_zero_coefficient :
    (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom
      (_root_.SerrePositivity.ComplexLimits.truncationExtendedZeroInclusion A ComplexShape.embeddingDownNat
        _root_.SerrePositivity.ComplexLimits.embeddingDownNat_eq_upIntLE_zero rfl (𝟙_ (Complex A))
        ((_root_.SerrePositivity.ComplexLimits.gammaDegreeZeroIso
          ((𝟙_ (Complex A)).truncLE' (ComplexShape.embeddingUpIntLE 0))).hom
            (gammaUnitSimplex A ⦋0⦌))) = (1 : A) := by
  rw [gammaUnitSimplex, _root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv_zero_raw,
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit_stdSimplex_eq_contraction]
  exact _root_.SerrePositivity.ComplexLimits.normalizedSimplexCochainAugmentation_zero_generator A

end SerrePositivity.EInfinity.PowerOperation
