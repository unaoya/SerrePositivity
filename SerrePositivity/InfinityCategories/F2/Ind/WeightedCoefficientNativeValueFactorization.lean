module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedCoefficientNativeValueComparison
public import SerrePositivity.InfinityCategories.F2.Ind.WeightedCoefficientNativeFiberPointedIso
public import SerrePositivity.InfinityCategories.F2.Ind.WeightedCoefficientJointPointedEvaluation
public import SerrePositivity.InfinityCategories.F2.Ind.WeightedCoefficientSourcePre

/-!
概要：元の native 制限全評価の pointed fiber 作用を、元の係数評価の同じ値作用へ因子分解。
方針：元の共同評価の pointed 係数公式と、元の指定値 fiber の包含を使う。
規約：元の全評価・係数評価・値 fiber を保持。使われ方：native 余錐の前合成同値の判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
  {I : Type u} [SmallCategory I] (F : I ⥤ RightFibrationObject C)
  (hF : ∀ v, IsIndVertex κ C
    ((HomotopyLimits.strictCoherentDiagram F ≫ rightStraighteningInfinityMap C).app
      (Opposite.op ⦋0⦌) v)) (i : I) (x : C _⦋0⦌)
local notation "G" => weightedDensityJointTargetDiagram F
local notation "Q" => weightedLeftCoefficientDiagram (F ⋙ rightFibrationOppositeOrdinary C) i
local notation "z" => weightedCoefficientNativeEvaluationVertex κ F hF i x
local notation "k" => CategoryTheory.Functor.map SSet.uliftFunctor
  (weightedCoefficientEvaluationBase F i x)

/-- 同じ定値標的へ戻した全評価の pointed 成分は、元の共同全評価の同じ制限。 -/
lemma weightedCoefficientNativeRestrictedMap_pointed :
    weightedCoefficientNativeRestrictedMap κ F hF i x ≫
      pullback.fst pointedSpaceProjection (SSet.const z) =
      weightedCoefficientRestrictedJointMap F i x ≫ pullback.fst pointedSpaceProjection G := by
  have h := congrArg (fun f ↦ f ≫ pullback.fst pointedSpaceProjection G)
    (weightedCoefficientNativeRestrictedMap_map κ F hF i x)
  simpa only [Category.assoc, leftUnstraighteningMap_pointed] using h

/-- 元の native 制限全評価の pointed fiber 作用は、同じ係数値作用の元の fiber 比較像。 -/
lemma weightedCoefficientNativeRestrictedMap_pointedFactorization :
    weightedCoefficientNativeRestrictedMap κ F hF i x ≫
      F2.constantUnstraighteningFiberProjection
        ((SSet.uliftFunctor.{u + 1, u}).obj (F.obj i).val.left) z =
      (SSet.uliftFunctor.{u + 1, u}).map (weightedCoefficientSourceValue F i x) ≫
        (weightedCoefficientNativeFiberPointedIso κ F hF i x).hom := by
  apply vertexFiber_hom_ext pointedSpaceProjection z
  rw [Category.assoc, F2.constantUnstraighteningFiberProjection, Category.assoc,
    constantPullbackFiberIso_fst_ι, weightedCoefficientNativeRestrictedMap_pointed]
  rw [Category.assoc, weightedCoefficientNativeFiberPointedIso_ι]
  rw [← Category.assoc
    ((SSet.uliftFunctor.{u + 1, u}).map (weightedCoefficientSourceValue F i x)),
    ← CategoryTheory.Functor.map_comp, weightedCoefficientSourceValue_ι]
  simp only [weightedCoefficientRestrictedJointMap, weightedCoefficientSourceIntoTotal,
    CategoryTheory.Functor.map_comp, Category.assoc]
  change (SSet.uliftFunctor.{u + 1, u}).map
    (twistedSourceElementsComparison (F.obj i).val.hom x) ≫
      ((SSet.uliftFunctor.{u + 1, u}).map (weightedTwistedCoefficientIntoTotal F i) ≫
        (SSet.uliftFunctor.{u + 1, u}).map (weightedDensityTwistedJointMap F) ≫
          smallLeftUnstraighteningPointedMap G) = _
  rw [weightedCoefficientJointEvaluation_pointed]
  rfl

/-- 同じ元の値写像は、元の係数値作用と元の pointed fiber 値比較の同じ合成。 -/
lemma weightedCoefficientNativeRestrictedValueMap_factorization :
    weightedCoefficientNativeRestrictedValueMap κ F hF i x =
      (SSet.uliftFunctor.{u + 1, u}).map (weightedCoefficientSourceValue F i x) ≫
        (weightedCoefficientNativeFiberPointedIso κ F hF i x).hom ≫
          (pointedSpaceFiberValueEquivalence z).hom := by
  rw [weightedCoefficientNativeRestrictedValueMap, ← Category.assoc,
    weightedCoefficientNativeRestrictedMap_pointedFactorization, Category.assoc]

end SerrePositivity.InfinityCategories.F2.Ind
