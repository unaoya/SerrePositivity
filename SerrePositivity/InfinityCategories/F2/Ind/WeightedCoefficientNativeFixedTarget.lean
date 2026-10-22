module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedCoefficientNativeGlobalComparison
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorIsPullbackIso

/-!
概要：元の始点固定族上の共同標的への相対 Hom を、同じ native 評価の定値標的へ戻す。
方針：同じ unstraightening の引き戻しが誘導する厳密な相対 Hom 同型を使う。
規約：元の全族・底・指定値を保持。使われ方：実際の native 評価 fiber 値写像への比較。
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

/-- 元の共同標的への全変換を、同じ native 評価の指定定値標的へ戻す同型。 -/
def weightedCoefficientNativeFixedTargetIso :
    relativeFunctorSpace (leftUnstraighteningProjection (SSet.const z :
      (SSet.uliftFunctor.{u + 1, u}).obj (F.obj i).val.left ⟶ SpaceInfinity.{u}))
      (weightedCoefficientNativeSourceBase F i x) ≅
    relativeFunctorSpace (leftUnstraighteningProjection G)
      (weightedCoefficientNativeGlobalBase F i x) :=
  relativeFunctorIsPullbackIso
    (leftUnstraighteningMap_isPullback (SSet.const z) G k
      (weightedCoefficientNativeEvaluationBase_target κ F hF i x))
    (weightedCoefficientNativeSourceBase F i x) (weightedCoefficientNativeGlobalBase F i x)
    (weightedCoefficientNativeSourceBase_global F i x)

/-- 元の同じ定値標的への変換を、同じ native 評価復元射で制限する。 -/
def weightedCoefficientNativeConstantPre :=
  relativeFunctorOverPre (leftUnstraighteningProjection (SSet.const z))
    (Over.homMk (weightedCoefficientNativeReconstructionLift κ F i x)
      (weightedCoefficientNativeReconstructionLift_projection κ F i x) :
      Over.mk (weightedCoefficientNativeSourceBase F i x) ⟶ Over.mk (leftUnstraighteningProjection D))

/-- 同じ定値標的内での制限と、同じ共同標的への厳密な相対 Hom 同型は可換。 -/
lemma weightedCoefficientNativeFixedTargetIso_source_vertex
    (v : (relativeFunctorSpace (leftUnstraighteningProjection (SSet.const z))
      (leftUnstraighteningProjection D)) _⦋0⦌) :
    (weightedCoefficientNativeFixedTargetIso κ F hF i x).hom.app (Opposite.op ⦋0⦌)
      ((weightedCoefficientNativeConstantPre κ F hF i x).app (Opposite.op ⦋0⦌) v) =
      (weightedCoefficientNativeReconstructionPre κ F i x).app (Opposite.op ⦋0⦌)
        ((weightedCoefficientNativeRelativeTargetMap κ F hF i x).app (Opposite.op ⦋0⦌) v) := by
  obtain ⟨M, hM, rfl⟩ := exists_relativeFunctorVertex _ _ v
  apply Subtype.ext
  change functorVertex ((weightedCoefficientNativeReconstructionLift κ F i x ≫ M) ≫
    leftUnstraighteningMap (SSet.const z) G k
      (weightedCoefficientNativeEvaluationBase_target κ F hF i x)) =
    functorVertex (weightedCoefficientNativeReconstructionLift κ F i x ≫ M ≫
      leftUnstraighteningMap (SSet.const z) G k
        (weightedCoefficientNativeEvaluationBase_target κ F hF i x))
  rw [Category.assoc]

end SerrePositivity.InfinityCategories.F2.Ind
