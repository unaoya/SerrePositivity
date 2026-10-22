module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedCoefficientNativeRestrictedMap

/-!
概要：元の native 評価余錐の実際の像を、同じ定値標的内で元の制限全評価へ比較する。
方針：共同標的内の相対同型を、同じ引き戻しが与える厳密な相対 Hom 同型で反映する。
規約：同じ native 余錐・復元射・全評価を保持。使われ方：実際の評価 fiber 値写像の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
  {I : Type u} [SmallCategory I] (F : I ⥤ RightFibrationObject C)
  (hF : ∀ v, IsIndVertex κ C
    ((HomotopyLimits.strictCoherentDiagram F ≫ rightStraighteningInfinityMap C).app
      (Opposite.op ⦋0⦌) v)) (i : I) (x : C _⦋0⦌)
local notation "G" => weightedDensityJointTargetDiagram F
local notation "D" => weightedCoefficientNativeEvaluationDiagram κ F i x
local notation "z" => weightedCoefficientNativeEvaluationVertex κ F hF i x
local notation "k" => CategoryTheory.Functor.map SSet.uliftFunctor
  (weightedCoefficientEvaluationBase F i x)

/-- 同じ native 評価余錐の実際の像は、同じ復元射上で同じ定値標的への全評価と同型。 -/
def weightedCoefficientNativeConstantComparisonIso : VertexIso
    ((weightedCoefficientNativeConstantPre κ F hF i x).app (Opposite.op ⦋0⦌)
      ((leftUnstraighteningMappingSpaceMap D (SSet.const z)).app (Opposite.op ⦋0⦌)
        (weightedCoefficientNativeCoconeTransformationVertex κ F hF i x)))
    (relativeFunctorVertex (leftUnstraighteningProjection (SSet.const z))
      (weightedCoefficientNativeSourceBase F i x) (weightedCoefficientNativeRestrictedMap κ F hF i x)
      (weightedCoefficientNativeRestrictedMap_projection κ F hF i x)) := by
  apply (qCatEquivalenceOfIso (weightedCoefficientNativeFixedTargetIso κ F hF i x)).isFullyFaithful
    |>.preimageVertexIso
  have hs := weightedCoefficientNativeFixedTargetIso_source_vertex κ F hF i x
    ((leftUnstraighteningMappingSpaceMap D (SSet.const z)).app (Opposite.op ⦋0⦌)
      (weightedCoefficientNativeCoconeTransformationVertex κ F hF i x))
  refine eqToIso (congrArg HomotopyCategory.mk hs) ≪≫
    weightedCoefficientNativeGlobalComparisonIso κ F hF i x ≪≫ ?_
  apply eqToIso
  apply congrArg HomotopyCategory.mk
  apply Subtype.ext
  change functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
    (weightedCoefficientSourceIntoTotal F i x) ≫ (SSet.uliftFunctor.{u + 1, u}).map
      (weightedDensityTwistedJointMap F) ≫ (smallLeftUnstraighteningIso G).hom) =
    functorVertex (weightedCoefficientNativeRestrictedMap κ F hF i x ≫
      leftUnstraighteningMap (SSet.const z) G k
        (weightedCoefficientNativeEvaluationBase_target κ F hF i x))
  rw [weightedCoefficientNativeRestrictedMap_map]
  rfl

end SerrePositivity.InfinityCategories.F2.Ind
