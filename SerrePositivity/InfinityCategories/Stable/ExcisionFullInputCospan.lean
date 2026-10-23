module
public import SerrePositivity.InfinityCategories.Stable.ExcisionInitialReplacementSquare
public import SerrePositivity.InfinityCategories.Stable.PosetInteriorPrism
public import SerrePositivity.InfinityCategories.Stable.ExcisionCorePunctured
public import SerrePositivity.InfinityCategories.Stable.ThinNerveMonomorphism
public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialJoinIso
public import SerrePositivity.InfinityCategories.Stable.ThinNerveConeComparison
public import SerrePositivity.InfinityCategories.Stable.PullbackConeVertex
public import SerrePositivity.InfinityCategories.F2.CatInfinity.ConeValEquality
public import SerrePositivity.InfinityCategories.Stable.ExcisionSquareGrid
public import SerrePositivity.InfinityCategories.Stable.ExcisionCoreCospanBoundary

/-!
概要：比較格子の初期角を実引き戻しへ置換し、矢印圏の普遍性へ接続する。
方針：穿孔格子の同じ錐と全非初期単体を厳密に保持する。
規約：一般安定性を仮定しない。使われ方：HA 1.4.2.15 の第二条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

def excisionFullInputCospanBoundary : (horn 2 2 : SSet.{u}) ⟶
    nerve ExcisionFullPuncturedIndex.{u} :=
  excisionCoreCospanBoundary ≫ nerveMap excisionCorePuncturedToFull.toFunctor

lemma excisionFullInputCospanBoundary_projection :
    excisionFullInputCospanBoundary.{u} ≫
      nerveMap (posetSubtypeInclusion IsExcisionFullPunctured) =
        cospanSquareBoundary ≫ excisionGridSquareEmbedding := by
  unfold excisionFullInputCospanBoundary
  rw [Category.assoc, excisionCorePuncturedToFull_projection, ← Category.assoc,
    excisionCoreCospanBoundary_projection, excisionGridCoreDiagram_lowerLeft]
  simp only [excisionGridSquareEmbedding, Category.assoc]

lemma excisionGridSquareEmbedding_initial :
    squareVertex excisionGridSquareEmbedding.{u} 0 0 = nerveVertex excisionGridInitialPoint := by
  apply CategoryTheory.nerve.ext_of_isThin
  funext i
  fin_cases i
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext <;> decide

lemma excisionFullInputCospanBoundary_leftAnodyne :
    leftAnodyneExtensions excisionFullInputCospanBoundary.{u} :=
  leftAnodyneExtensions.comp_mem _ _ excisionCoreCospanBoundary_leftAnodyne
    excisionCorePuncturedToFull_leftAnodyne

end SerrePositivity.InfinityCategories
