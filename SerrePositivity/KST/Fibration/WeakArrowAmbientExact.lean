module
public import SerrePositivity.KST.Fibration.WeakStringCofibers
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.TrivialFibrationSquares

/-! # 元の W 辺図式の包含の完全性

全相対 cofiber 図式への完全な切断と底辺射影から、元の全部分図式圏の包含を回収する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- W 辺図式の元の包含は、零対象と全 cofiber 正方形を保つ。 -/
lemma weakArrowInclusion_preservesCofiberData {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    PreservesCofiberData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakArrowPredicate q)).ι := by
  have hp : PreservesCofiberData (cofiberProjection B.obj) :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesCofiber⟩
  have h := (weakArrowCofiberEquivalence q).inv.property.comp
    ((relativeCofiberInclusion (ClosedStablePredicate.top (sInputModel B))
      (kernelClosedPredicate q)).property.comp hp)
  have he : (weakArrowCofiberEquivalence q).inv.val ≫
      ((relativeCofiberInclusion (ClosedStablePredicate.top (sInputModel B))
        (kernelClosedPredicate q)).val ≫ cofiberProjection B.obj) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakArrowPredicate q)).ι := by
    rw [← weakCofiberProjection_ι, ← weakArrowCofiberEquivalence_hom, ← Category.assoc]
    change ((weakArrowCofiberEquivalence q).inv ≫
      (weakArrowCofiberEquivalence q).hom).val ≫ _ = _
    rw [weakArrowCofiberEquivalence_inv_hom]
    rfl
  rwa [he] at h

/-- 元の全 W 辺図式を周囲の全矢図式へ含める完全関手。 -/
def weakArrowAmbientInclusion {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    weakArrowModel q ⟶ ambientDiagramModel (Δ[1] : SSet.{u}) B :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakArrowPredicate q)).ι,
    weakArrowInclusion_preservesCofiberData q⟩

end SerrePositivity.KST.Fibration
