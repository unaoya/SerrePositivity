module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedIndCoefficientRestriction
public import SerrePositivity.InfinityCategories.F2.Ind.HomotopyTransformationClassIso

/-!
概要：指定単位を保持する相対 join の厳密化後も、元の係数変換の同じ変換空間内の類を保持。
方針：元の全単位の h Fun の一致を係数包含で制限し、正規化した端点で同じ変換頂点へ戻す。
規約：元の係数図式と分類頂点を固定。使われ方：元の係数余極限性の厳密化後への移送。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
  {I : Type u} [SmallCategory I] (F : I ⥤ RightFibrationObject C)
  (hF : ∀ v, IsIndVertex κ C
    ((HomotopyLimits.strictCoherentDiagram F ≫ rightStraighteningInfinityMap C).app
      (Opposite.op ⦋0⦌) v)) (i : I)

/-- 同じ相対 join の prism から得る全単位を、元の係数図式上へ制限する。 -/
def weightedIndRelativeCoefficientHomotopy := weightedIndCoefficientRestriction κ F hF
  (weightedIndDensityRelativeHomotopy κ F hF) i

/-- 同じ係数図式と分類頂点で正規化しても、元の係数単位の h Fun の類は保たれる。 -/
lemma weightedIndRelativeCoefficientHomotopy_hom_eq :
    SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (weightedIndRelativeCoefficientHomotopy κ F hF i)) =
      SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (weightedIndDensityCoefficientHomotopy κ F hF i)) := by
  let a := (SSet.uliftFunctor.{u + 1, u}).map
    (weightedNerveConstantLift (rightFibrationTotalDiagram F) i)
  have hp := kanFunctorHomotopy_precomp_hom_arrow
    (weightedIndDensityRelativeHomotopy κ F hF) (weightedIndDensityHomotopy κ F hF)
    (congrArg Arrow.mk (weightedIndDensityRelativeHomotopy_hom_eq κ F hF)) a
  have h₁ := kanFunctorHomotopy_hom_arrow_of_h_eq
    (weightedIndRelativeCoefficientHomotopy κ F hF i)
    (functorHomotopyPrecomp (weightedIndDensityRelativeHomotopy κ F hF) a) rfl
  have h₂ := kanFunctorHomotopy_hom_arrow_of_h_eq
    (weightedIndDensityCoefficientHomotopy κ F hF i)
    (functorHomotopyPrecomp (weightedIndDensityHomotopy κ F hF) a) rfl
  apply Arrow.mk_injective _ _
  exact h₁.trans (hp.trans h₂.symm)

/-- 元の係数単位と相対 join の同じ係数単位は、同じ変換空間内で同型。 -/
def weightedIndRelativeCoefficientTransformationIso :
    VertexIso (homotopyTransformationVertex (weightedIndRelativeCoefficientHomotopy κ F hF i))
      (homotopyTransformationVertex (weightedIndDensityCoefficientHomotopy κ F hF i)) :=
  homotopyTransformationClassIso _ _ (weightedIndRelativeCoefficientHomotopy_hom_eq κ F hF i)

end SerrePositivity.InfinityCategories.F2.Ind
