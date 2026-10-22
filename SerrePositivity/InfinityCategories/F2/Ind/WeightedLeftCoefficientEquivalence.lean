module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedLeftCoefficientRecovery

/-!
概要：共同 weighted 分類の同じ係数復元は、追加の同値性仮定なしに前合成同値。
方針：元の復元射の底変換の同値を、元のグラフ同型と小さい底変換同型で移す。
規約：元の同じ復元写像の同値性。使われ方：指定係数密度の native な余極限性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {B : SSet.{u}} [Quasicategory B] {I : Type u} [SmallCategory I]
  (F : I ⥤ LeftFibrationObject B) (i : I)

/-- 元の同じ係数復元射は、元の全関手空間で前合成同値を与える。 -/
lemma weightedLeftCoefficientRecovery_isPrecompositionEquivalence :
    IsPrecompositionEquivalence (weightedLeftCoefficientRecovery F i) := by
  have : Quasicategory (B ⊗ nerve I) :=
    quasicategory_of_innerFibration (fst B (nerve I))
  let p := leftFibrationWeightedProjection F
  let J := leftStraighteningInfinityDiagram p
  let g := underSectionFiberBase B i
  exact (isPrecompositionEquivalence_of_iso
    (weightedParameterGraphIso (leftFibrationDiagramProjection F) i)).comp
      ((fiberComparisonBaseChange_isPrecompositionEquivalence p
        (smallLeftUnstraighteningProjection J) (leftStraighteningInfinityReconstruction p)
        (leftStraighteningInfinityReconstruction_projection p)
        (leftStraighteningInfinityReconstruction_isPrecompositionEquivalence p) g).comp
          (isPrecompositionEquivalence_of_iso (smallLeftUnstraighteningBaseChangeIso J g).symm))

/-- 同じ係数復元の各値での実際の fiber 写像も、元の指定値を保つ同値。 -/
lemma weightedLeftCoefficientRecovery_fiber_isQCatEquivalence (b : B _⦋0⦌) :
    IsQCatEquivalence (vertexFiberMap (F.obj i).val.hom
      (smallLeftUnstraighteningProjection (weightedLeftCoefficientDiagram F i))
      (weightedLeftCoefficientRecovery F i)
      (weightedLeftCoefficientRecovery_projection F i) b) := by
  have : LeftFibration (F.obj i).val.hom := (F.obj i).property
  exact vertexFiberMap_isQCatEquivalence_of_precompositionEquivalence _ _ _
    (weightedLeftCoefficientRecovery_projection F i)
    (weightedLeftCoefficientRecovery_isPrecompositionEquivalence F i) b

end SerrePositivity.InfinityCategories.F2.Ind
