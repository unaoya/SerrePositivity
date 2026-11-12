module

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedTransformationTriangle
public import SerrePositivity.KST.Spectra.EnrichedOrderedCylinderNerve

/-!
概要：豊穣な因子分解の三段の円柱を、元の三つの関手へ厳密に制限する。
方針：各段の包含後の Hom を定義で計算する。
規約：関手としての等式。使われ方：零角の三角形の頂点図式の検査。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.EnrichedTransformationTriangle
variable {C : Type v} {D : Type w} [EnrichedCategory SSet.{u} C] [EnrichedCategory SSet.{u} D]
  (F G H : EnrichedFunctor SSet.{u} C D)
  (η : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F G)
  (θ : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) G H)
  (ζ : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F H)
  (hc : ∀ X, ζ.app X = (λ_ (𝟙_ SSet.{u})).inv ≫
    (η.app X ⊗ₘ θ.app X) ≫ eComp SSet (F.obj X) (G.obj X) (H.obj X))

/-- 因子分解の最初の段は元の最初の関手。 -/
lemma functor_stage_zero :
    (EnrichedOrderedCylinder.stageInclusion (C := C) (0 : Fin 3)).comp SSet
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedTransformationTriangle.functor F G H η θ ζ hc) = F := by
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro X Y
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro f
  rfl

/-- 因子分解の中間の段は元の中間の関手。 -/
lemma functor_stage_one :
    (EnrichedOrderedCylinder.stageInclusion (C := C) (1 : Fin 3)).comp SSet
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedTransformationTriangle.functor F G H η θ ζ hc) = G := by
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro X Y
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro f
  rfl

/-- 因子分解の最後の段は元の最後の関手。 -/
lemma functor_stage_two :
    (EnrichedOrderedCylinder.stageInclusion (C := C) (2 : Fin 3)).comp SSet
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedTransformationTriangle.functor F G H η θ ζ hc) = H := by
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro X Y
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro f
  rfl

end SerrePositivity.KST.Spectra.EnrichedTransformationTriangle
