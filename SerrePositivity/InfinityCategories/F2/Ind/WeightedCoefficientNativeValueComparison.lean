module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedCoefficientNativeConstantComparison
public import SerrePositivity.InfinityCategories.F2.CoconeFiberValueMap
public import SerrePositivity.InfinityCategories.F2.ConstantUnstraighteningValueOverPre
public import SerrePositivity.InfinityCategories.F2.ConstantTargetVertex

/-!
概要：元の native 評価余錐の実際の fiber 値写像を、元の制限全評価の値写像へ比較する。
方針：同じ定値標的内の相対同型を値へ写し、native fiber 値写像の標準変換公式を使う。
規約：元の余錐・復元射・指定値を保持。使われ方：指定係数余錐の実際の余極限判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
  {I : Type u} [SmallCategory I] (F : I ⥤ RightFibrationObject C)
  (hF : ∀ v, IsIndVertex κ C
    ((HomotopyLimits.strictCoherentDiagram F ≫ rightStraighteningInfinityMap C).app
      (Opposite.op ⦋0⦌) v)) (i : I) (x : C _⦋0⦌)
local notation "D" => weightedCoefficientNativeEvaluationDiagram κ F i x
local notation "z" => weightedCoefficientNativeEvaluationVertex κ F hF i x
local notation "A" => CategoryTheory.Functor.obj SSet.uliftFunctor
  (twistedSourceElements (weightedCoefficientProjection F i) x)

/-- 元の全評価の同じ係数・始点制限を、元の指定 native 評価頂点の値への射で読む。 -/
def weightedCoefficientNativeRestrictedValueMap :=
  weightedCoefficientNativeRestrictedMap κ F hF i x ≫
    F2.constantUnstraighteningFiberProjection
      ((SSet.uliftFunctor.{u + 1, u}).obj (F.obj i).val.left) z ≫
        (pointedSpaceFiberValueEquivalence z).hom

/-- 同じ定値標的への全変換を、同じ指定値への全空間写像へ送る。 -/
def weightedCoefficientNativeConstantValueMap :=
  (F2.constantUnstraighteningRelativeIso (weightedCoefficientNativeSourceBase F i x) z).hom ≫
    (ihom A).map (pointedSpaceFiberValueEquivalence z).hom

/-- 同じ native 余錐の実際の fiber 値写像は、同じ復元射上で元の制限全評価と関手同型。 -/
def weightedCoefficientNativeValueComparisonIso :
    FunctorIso (weightedCoefficientNativeReconstructionLift κ F i x ≫
      F2.coconeFiberValueMapAt (weightedCoefficientNativeEvaluationCocone κ F hF i x) z
        (weightedCoefficientNativeEvaluationCocone_vertex κ F hF i x))
      (weightedCoefficientNativeRestrictedValueMap κ F hF i x) := by
  have he := (weightedCoefficientNativeConstantComparisonIso κ F hF i x).map
    (weightedCoefficientNativeConstantValueMap κ F hF i x)
  have hs := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌)
    ((leftUnstraighteningMappingSpaceMap D (SSet.const z)).app (Opposite.op ⦋0⦌)
      (weightedCoefficientNativeCoconeTransformationVertex κ F hF i x)))
    (F2.constantUnstraighteningRelativeIso_value_overPre (leftUnstraighteningProjection D)
      (weightedCoefficientNativeSourceBase F i x) (weightedCoefficientNativeReconstructionLift κ F i x)
      (weightedCoefficientNativeReconstructionLift_projection κ F i x) z)
  change (weightedCoefficientNativeConstantValueMap κ F hF i x).app (Opposite.op ⦋0⦌)
    ((weightedCoefficientNativeConstantPre κ F hF i x).app (Opposite.op ⦋0⦌)
      ((leftUnstraighteningMappingSpaceMap D (SSet.const z)).app (Opposite.op ⦋0⦌)
        (weightedCoefficientNativeCoconeTransformationVertex κ F hF i x))) =
    ((pre (weightedCoefficientNativeReconstructionLift κ F i x)).app _).app (Opposite.op ⦋0⦌)
      ((F2.coherentConstantTargetMap D z).app (Opposite.op ⦋0⦌)
        (weightedCoefficientNativeCoconeTransformationVertex κ F hF i x)) at hs
  have hv := F2.coconeFiberValueMapAt_vertex
    (weightedCoefficientNativeEvaluationCocone κ F hF i x) z
    (weightedCoefficientNativeEvaluationCocone_vertex κ F hF i x)
  change functorVertex (F2.coconeFiberValueMapAt
    (weightedCoefficientNativeEvaluationCocone κ F hF i x) z
    (weightedCoefficientNativeEvaluationCocone_vertex κ F hF i x)) =
      (F2.coherentConstantTargetMap D z).app (Opposite.op ⦋0⦌)
        (weightedCoefficientNativeCoconeTransformationVertex κ F hF i x) at hv
  rw [← hv] at hs
  refine eqToIso (congrArg HomotopyCategory.mk hs.symm) ≪≫ he ≪≫ ?_
  apply eqToIso
  apply congrArg HomotopyCategory.mk
  change ((ihom A).map (pointedSpaceFiberValueEquivalence z).hom).app (Opposite.op ⦋0⦌)
    ((F2.constantUnstraighteningRelativeIso (weightedCoefficientNativeSourceBase F i x) z).hom.app _
      (relativeFunctorVertex _ _ (weightedCoefficientNativeRestrictedMap κ F hF i x)
        (weightedCoefficientNativeRestrictedMap_projection κ F hF i x))) = _
  rw [F2.constantUnstraighteningRelativeIso_vertex]
  rfl

end SerrePositivity.InfinityCategories.F2.Ind
