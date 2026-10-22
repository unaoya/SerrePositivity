module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedIndRelativeFiberCoefficient
public import SerrePositivity.InfinityCategories.F2.Ind.CoconeTransformationPointPrism
public import SerrePositivity.InfinityCategories.F2.Ind.RelativeJoinFiberPrism

/-!
概要：実際の相対 join fiber 余錐の標準変換は、元の全単位の同じ係数制限そのもの。
方針：元の fiber prism の厳密な公式を、同じ weighted fiber 同型で前合成して比較する。
規約：元の全円柱と指定頂点を保持。使われ方：実際の fiber 余錐の余極限性の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
  {I : Type u} [PartialOrder I] (F : I ⥤ RightFibrationObject C)
  (hF : ∀ v, IsIndVertex κ C
    ((HomotopyLimits.strictCoherentDiagram F ≫ rightStraighteningInfinityMap C).app
      (Opposite.op ⦋0⦌) v)) (i : I)
local notation "p" => weightedIndDensityIndexProjection F
local notation "v" => ULift.up (nerveVertex i)
local notation "e" => weightedIndCoefficientFiberIso F i
local notation "H" => weightedIndDensityRelativeDiagram κ F hF
local notation "D" => weightedIndCoefficientDiagram κ F i
local notation "z" => weightedIndCoefficientVertex κ F hF i
local notation "A" => CategoryTheory.Functor.obj SSet.uliftFunctor
  (CategoryTheory.Functor.obj (rightFibrationTotalDiagram F) i)
local notation "K" => CategoryTheory.Functor.obj SSet.uliftFunctor
  (weightedNerve (rightFibrationTotalDiagram F))

/-- 元の実際の fiber 余錐を係数へ戻して得る、元の図式と頂点での標準変換。 -/
def weightedIndRelativeFiberCoefficientTransformationVertex :=
  (F2.coconeTransformationMap D z).app (Opposite.op ⦋0⦌)
    (F2.coconeMappingPointAt (weightedIndRelativeFiberCoefficientCocone κ F hF i) z
      (weightedIndRelativeFiberCoefficientCocone_vertex κ F hF i))

/-- 同じ実際の fiber 余錐の標準変換は、元の相対 join 全単位の同じ係数制限に厳密に一致。 -/
lemma weightedIndRelativeFiberCoefficientTransformationVertex_eq :
    weightedIndRelativeFiberCoefficientTransformationVertex κ F hF i =
      homotopyTransformationVertex (weightedIndRelativeCoefficientHomotopy κ F hF i) := by
  have ha : fatJoinCylinderMap (e).hom (𝟙 (Δ[0] : SSet.{u + 1})) ≫
      fst ((vertexFiber p v) ⊗ (Δ[1] : SSet.{u + 1})) Δ[0] ≫
        (vertexFiberι p v ▷ (Δ[1] : SSet.{u + 1})) =
      fst (A ⊗ (Δ[1] : SSet.{u + 1})) Δ[0] ≫
        ((SSet.uliftFunctor.{u + 1, u}).map
          (weightedNerveConstantLift (rightFibrationTotalDiagram F) i) ▷ Δ[1]) := by
    have h₀ : fatJoinCylinderMap (e).hom (𝟙 (Δ[0] : SSet.{u + 1})) ≫
        fst ((vertexFiber p v) ⊗ (Δ[1] : SSet.{u + 1})) Δ[0] ≫
          (vertexFiberι p v ▷ (Δ[1] : SSet.{u + 1})) =
        fst (A ⊗ (Δ[1] : SSet.{u + 1})) Δ[0] ≫
          (((e).hom ≫ vertexFiberι p v) ▷ Δ[1]) := rfl
    rw [uliftWeightedIndDensityFiberIso_ι F i] at h₀
    exact h₀
  have hp := congrArg (fun f ↦ fatJoinCylinderMap (e).hom (𝟙 (Δ[0] : SSet.{u + 1})) ≫ f ≫ H)
    (relativeJoinFiberEmbedding_prism p v)
  have hq := congrArg (fun f ↦ f ≫ (β_ K (Δ[1] : SSet.{u + 1})).hom ≫ relativeJoinPrism p ≫ H) ha
  simp only [Category.assoc] at hp hq
  unfold weightedIndRelativeFiberCoefficientTransformationVertex
  apply SSet.yonedaEquiv.symm.injective
  apply F2.constantTransformationPrism_injective
  rw [coconeTransformationPointAt_prism, homotopyTransformationVertex_prism,
    weightedIndRelativeFiberCoefficientCocone_val]
  change joinCylinderMap A Δ[0] ≫
    (joinMap (e).hom (𝟙 (Δ[0] : SSet.{u + 1})) ≫ relativeJoinFiberEmbedding p v ≫ H) =
      fst (A ⊗ (Δ[1] : SSet.{u + 1})) Δ[0] ≫
        ((SSet.uliftFunctor.{u + 1, u}).map
          (weightedNerveConstantLift (rightFibrationTotalDiagram F) i) ▷ Δ[1]) ≫
        (β_ K (Δ[1] : SSet.{u + 1})).hom ≫ relativeJoinPrism p ≫ H
  rw [← Category.assoc, ← joinCylinderMap_naturality]
  simpa only [Category.assoc] using hp.trans hq

end SerrePositivity.InfinityCategories.F2.Ind
