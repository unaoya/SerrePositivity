module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedCoefficientNativeEvaluation
public import SerrePositivity.InfinityCategories.F2.Ind.PresheafDensityRestrictedTransformation

/-!
概要：元の native 係数余錐の評価変換は、元の共同密度変換の同じ係数・始点制限。
方針：同じ全円柱を curry の評価公式で比較し、元の変換頂点へ戻す。
規約：元の native 評価の両端を保持。使われ方：実際の評価余錐の c1 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
  {I : Type u} [SmallCategory I] (F : I ⥤ RightFibrationObject C)
  (hF : ∀ v, IsIndVertex κ C
    ((HomotopyLimits.strictCoherentDiagram F ≫ rightStraighteningInfinityMap C).app
      (Opposite.op ⦋0⦌) v)) (i : I) (x : C _⦋0⦌)
local notation "W" => weightedNerve (rightFibrationTotalDiagram F)

/-- 元の native 係数円柱の評価は、元の共同全円柱の同じ係数・始点での制限。 -/
lemma weightedCoefficientNativeEvaluationHomotopy_h :
    (weightedCoefficientNativeEvaluationHomotopy κ F hF i x).h =
      ((SSet.uliftFunctor.{u + 1, u}).map (weightedCoefficientEvaluationBase F i x) ▷
        (Δ[1] : SSet.{u + 1})) ≫ (weightedDensityJointHomotopy F).h := by
  change (weightedIndDensityCoefficientHomotopy κ F hF i).h ≫
    (indInclusionPresheaf κ C ≫ presheafInfinityEvaluation x) = _
  rw [← Category.assoc, weightedIndDensityCoefficientHomotopy_inclusion, Category.assoc]
  change ((SSet.uliftFunctor.{u + 1, u}).map
    (weightedNerveConstantLift (rightFibrationTotalDiagram F) i) ▷ (Δ[1] : SSet.{u + 1})) ≫
      (curry ((α_ ((SSet.uliftFunctor.{u + 1, u}).obj C.op)
        ((SSet.uliftFunctor.{u + 1, u}).obj W) (Δ[1] : SSet.{u + 1})).inv ≫
          (((HomotopyLimits.uliftTensorIso.{u, u + 1} C.op W).inv ▷
            (Δ[1] : SSet.{u + 1})) ≫ (weightedDensityJointHomotopy F).h)) ≫
              evaluateFunctorAt (ULift.up (SSet.opObjEquiv.symm x))) = _
  rw [curry_evaluateFunctorAt_vertex]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro z
  rfl

/-- 元の native 係数変換頂点を、元の包含と指定始点で評価した指定頂点。 -/
def weightedCoefficientNativeEvaluatedTransformation :=
  (F2.constantTransformationPost (weightedIndCoefficientDiagram κ F i)
    (weightedIndCoefficientVertex κ F hF i) (indPresheafEvaluation κ x)).app
      (Opposite.op ⦋0⦌)
      (homotopyTransformationVertex (weightedIndDensityCoefficientHomotopy κ F hF i))

/-- 同じ評価された変換頂点は、元の native 評価円柱の指定頂点そのもの。 -/
lemma weightedCoefficientNativeEvaluatedTransformation_eq :
    weightedCoefficientNativeEvaluatedTransformation κ F hF i x =
      homotopyTransformationVertex (weightedCoefficientNativeEvaluationHomotopy κ F hF i x) := by
  apply SSet.yonedaEquiv.symm.injective
  apply F2.constantTransformationPrism_injective
  change F2.constantTransformationPrism (SSet.yonedaEquiv.symm
    ((F2.constantTransformationPost (weightedIndCoefficientDiagram κ F i)
      (weightedIndCoefficientVertex κ F hF i) (indPresheafEvaluation κ x)).app (Opposite.op ⦋0⦌)
        (homotopyTransformationVertex (weightedIndDensityCoefficientHomotopy κ F hF i)))) = _
  rw [← SSet.yonedaEquiv_symm_comp, F2.constantTransformationPost_prism,
    homotopyTransformationVertex_prism, homotopyTransformationVertex_prism]
  rfl

end SerrePositivity.InfinityCategories.F2.Ind
