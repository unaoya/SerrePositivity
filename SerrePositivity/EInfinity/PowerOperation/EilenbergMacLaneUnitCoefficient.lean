module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneGammaUnitPoint
public import SerrePositivity.EInfinity.AlexanderWhitney.SimplexCounitContraction
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedSimplexCochainAugmentationZero

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
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.ComplexLimits
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- Γ の指定 AW 単位の係数は、同じ零次数の比較の下で一である。 -/
lemma gammaUnitSimplex_zero_coefficient :
    (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom
      (truncationExtendedZeroInclusion A ComplexShape.embeddingDownNat
        embeddingDownNat_eq_upIntLE_zero rfl (𝟙_ (Complex A))
        ((gammaDegreeZeroIso
          ((𝟙_ (Complex A)).truncLE' (ComplexShape.embeddingUpIntLE 0))).hom
            (gammaUnitSimplex A ⦋0⦌))) = (1 : A) := by
  rw [gammaUnitSimplex, normalizedSimplexHomEquiv_zero_raw,
    AlexanderWhitney.cochainCounit_stdSimplex_eq_contraction]
  exact normalizedSimplexCochainAugmentation_zero_generator A

end SerrePositivity.EInfinity.PowerOperation
