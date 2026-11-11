module

public import SerrePositivity.EInfinity.BarrattEccles.HigherComparisonComponents
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowValue

/-!
# 元の全 E 代数の reduced hammock と同じ普通の局所化への評価

概要：既存の元の高次比較の右射を元の局所化 Hom へ評価する。
方針：全語の評価と同じ正規化同型を使い、三本矢の値へ戻す。
規約：任意の可換環と元の全代数・元の分解・元の零単体を保持する。
使われ方：高次比較が誘導する π₀ と既存の同値の一致。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra Opposite Hammock
open scoped Simplicial
variable (A : Type u) [CommRing A]

def algebraReducedHammockValue (X Y : (operad A).Algebra) :
    let := modelCategory A
    algebraReducedHammock A X Y ⟶ (Functor.const SimplexCategoryᵒᵖ).obj
      ((weakEquivalences (operad A).Algebra).Q.obj X ⟶
        (weakEquivalences (operad A).Algebra).Q.obj Y) := by
  let := modelCategory A
  exact UniverseValue.reducedValue (weakEquivalences (operad A).Algebra).Q
    (weakEquivalences (operad A).Algebra).Q_inverts X Y

lemma algebraReducedHammockValue_reduction (X Y : (operad A).Algebra) :
    let := modelCategory A
    (algebraHammockReductionIso A X Y).hom ≫ algebraReducedHammockValue A X Y =
      UniverseValue.colimitValue (weakEquivalences (operad A).Algebra).Q
        (weakEquivalences (operad A).Algebra).Q_inverts X Y := by
  let := modelCategory A
  change (reducedColimitIso (weakEquivalences (operad A).Algebra) X Y).hom ≫
    (reducedAugmentation (weakEquivalences (operad A).Algebra) X Y ≫ _) = _
  rw [← reducedColimitIso_inv, Iso.hom_inv_id_assoc]

lemma mappingSpaceReducedHammockNerveMap_value (X Y : (operad A).Algebra) :
    let := modelCategory A
    mappingSpaceReducedHammockNerveMap A X Y ≫ algebraReducedHammockValue A X Y =
      mappingSpaceHammockGraphNerveMap A X Y ≫
        UniverseValue.graphMap (weakEquivalences (operad A).Algebra).Q
          (weakEquivalences (operad A).Algebra).Q_inverts := by
  let := modelCategory A
  rw [mappingSpaceReducedHammockNerveMap, Category.assoc, algebraReducedHammockValue_reduction]
  change (mappingSpaceHammockGraphNerveMap A X Y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion (weakEquivalences (operad A).Algebra) X Y _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.threeArrow) ≫ _ = _
  rw [Category.assoc, UniverseValue.graphInclusion_colimitValue]

lemma mappingSpaceReducedHammockNerveMap_value_zero (X Y : (operad A).Algebra)
    (f : (((mappingSpace A).obj (op X)).obj Y) _⦋0⦌) :
    let := modelCategory A
    (algebraReducedHammockValue A X Y).app (op ⦋0⦌)
      ((mappingSpaceReducedHammockNerveMap A X Y).app (op ⦋0⦌)
        (ComposableArrows.mk₀ (show ULiftHom.{u + 1}
          (((((mappingSpace A).obj (op X)).obj Y).Elements)ᵒᵖ) from
            op ((((mappingSpace A).obj (op X)).obj Y).elementsMk (op ⦋0⦌) f)))) =
      mappingSpacePiZeroEquiv A (weakEquivalences (operad A).Algebra).Q
        (op X) Y (SSet.π₀.mk f) := by
  let := modelCategory A
  let k := ComposableArrows.mk₀ (show ULiftHom.{u + 1}
    (((((mappingSpace A).obj (op X)).obj Y).Elements)ᵒᵖ) from
      op ((((mappingSpace A).obj (op X)).obj Y).elementsMk (op ⦋0⦌) f))
  have h := congrArg (fun m => m.app (op ⦋0⦌) k)
    (mappingSpaceReducedHammockNerveMap_value A X Y)
  exact h.trans ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.special_value _).trans
    (mappingSpaceSpecialHammockValue_zero A X Y f))

end SerrePositivity.EInfinity.BarrattEccles
