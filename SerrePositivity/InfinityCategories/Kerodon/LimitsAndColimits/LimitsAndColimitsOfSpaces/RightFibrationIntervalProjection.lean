module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.RightFibrationMappingOverNaturality
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.PinchedUniversal
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceIntervalComparison

/-!
概要：span の元の Hom 射影を区間模型へ送る全族の式。
方針：正規化した slice の包含、錐の uncurry、右 prism の三段を照合する。
規約：一点の終点のみを扱い、一般の図式形状への拡張は行わない。
使われ方：G8 の辺形状 Δ[1] の第一面と長辺の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open TheSliceAndJoinConstructions IsomorphismsAndIsofibrations MorphismSpaces
open FullFaithfulAndEssentiallySurjectiveFunctors
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

/-- 概要：Hom 射影の join 展開は、元の同じ全錐を底へ送った射そのもの。
方針：正規化した fiber の包含の式を uncurry し、後合成の既存公式を使う。
規約：r に充填性を要求しない。使われ方：第一面の区間比較の独立した核。 -/
lemma rightFibrationMappingHomProjection_pinchedUncurry {A E B : SSet.{u}}
    (r : E ⟶ B) (c : E _⦋0⦌) (x : B _⦋0⦌)
    (f : A ⟶ rightFibrationMappingTotal r c x) :
    pinchedHomUncurry (f ≫ rightFibrationMappingHomProjection r c x) =
      sliceOverUncurry
        (f ≫ vertexFiberι (sliceOverProjection (SSet.yonedaEquiv.symm c) ≫ r) x) ≫ r := by
  unfold pinchedHomUncurry
  simp only [Category.assoc]
  rw [rightFibrationMappingHomProjection_normalized_ι]
  rw [← Category.assoc, pointSlicePostcomp_uncurry]

/-- 概要：元の Hom 射影から区間模型への全族は、同じ実錐を右 prism で読む射と一致。
方針：pinched/interval 比較の既存の展開式と、上の join 展開の厳密な等式を使う。
規約：全パラメータ A を保持する。使われ方：辺の三角形族の第一面・長辺。 -/
lemma rightFibrationMappingHomProjection_intervalUncurry {A E B : SSet.{u}}
    (r : E ⟶ B) (c : E _⦋0⦌) (x : B _⦋0⦌)
    (f : A ⟶ rightFibrationMappingTotal r c x) :
    intervalMappingUncurry
        (f ≫ rightFibrationMappingHomProjection r c x ≫
          pinchedHomToIntervalMappingSpace x (r.app _ c)) =
      rightMappingSpacePrism A ≫ sliceOverUncurry
        (f ≫ vertexFiberι (sliceOverProjection (SSet.yonedaEquiv.symm c) ≫ r) x) ≫ r := by
  rw [← Category.assoc, pinchedHomToIntervalMappingSpace_uncurry,
    rightFibrationMappingHomProjection_pinchedUncurry]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
