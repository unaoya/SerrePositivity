module
public import SerrePositivity.EInfinity.HomotopyWeight.ConePoints

/-!
概要：元のtensor frameの零次Homと重み付き錐の同じ標準点を照合する。
方針：二つの随伴の合成と、元の零次同型に関する自然性を計算する。
規約：IS-W2 R03の既存単位則。frame・重み・零単体の表示を保持。
使われ方：普遍frame錐をnative制限へ追跡する標準点の同定。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits HomotopicalAlgebra
open scoped Simplicial
open SerrePositivity.DiagramModel
variable (K : Type u) [SmallCategory K] {C : Type v} [Category.{u} C]
  [HasColimitsOfSize.{u,u} C] [ModelCategory C]
  (W : Kᵒᵖ ⥤ SSet.{u}) (B : K ⥤ SimplexCategory ⥤ C)

/-- 同じ零次同型を前置したHomは、元の同じ重み付き錐の零単体に写る。 -/
theorem tensorFrameHomIso_point (Y : C)
    (f : (FrameWeightRealization.functor K B).obj W ⟶ Y) :
    (((tensorFrameHomIso K W B).hom.app Y).app (Opposite.op ⦋0⦌))
      ((tensorFrameZeroIso K W B).hom ≫ f) =
        conePoint Kᵒᵖ W ((FrameWeightRealization.adjunction K B).homEquiv W Y f) := by
  change SSet.yonedaEquiv ((tensorRealizationAdjunction K W B).homEquiv _ Y (_ ≫ f)) =
    SSet.yonedaEquiv ((WeightedCones.adjunction Kᵒᵖ W).homEquiv _ _
      ((zeroTensorWeightIso Kᵒᵖ W).hom ≫
        (FrameWeightRealization.adjunction K B).homEquiv W Y f))
  simp only [tensorRealizationAdjunction, Adjunction.comp_homEquiv]
  exact congrArg (fun h => SSet.yonedaEquiv ((WeightedCones.adjunction Kᵒᵖ W).homEquiv _ _ h))
    ((FrameWeightRealization.adjunction K B).homEquiv_naturality_left _ f)

end SerrePositivity.EInfinity.HomotopyWeight
