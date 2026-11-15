module

public import SerrePositivity.HomotopicalAlgebra.Diagram.FrameBousfieldKanAugmentationFrames
public import SerrePositivity.HomotopicalAlgebra.Diagram.ElementsCopowerAugmentation
public import SerrePositivity.HomotopicalAlgebra.Diagram.ElementsBousfieldKanWeight

/-!
概要：検証済みの増大射保存則を、実際に用いる表示同型の順方向へ移す。
方針：同じ同型の逆を前合成し、既存の係数移送・要素圏表示の法則を使う。
使われ方：HTT 4.2.4.4、RR02(a)の評価表示同型の合成。
規約：同型と余錐の選択を変更しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w u
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.DiagramModel
variable {K : Type w} [SmallCategory K]
  {C : Type u} [Category.{w} C] [HasColimitsOfSize.{w, w} C]

namespace FrameWeightRealization
lemma augmentation_frameIso {A B : K ⥤ SimplexCategory ⥤ C} (e : A ≅ B)
    (c : Cocone (ConstantWeightHom.degree K A (SimplexCategory.mk 0))) :
    ((family K).mapIso e).hom.app (bousfieldKanWeight Kᵒᵖ) ≫
        bousfieldKanAugmentation B
          ((Cocone.precompose (ConstantWeightRealization.degreeMap K e.inv
            (SimplexCategory.mk 0))).obj c) = bousfieldKanAugmentation A c := by
  let i := ((family K).mapIso e).app (bousfieldKanWeight Kᵒᵖ)
  apply (cancel_epi i.inv).mp
  change i.inv ≫ (i.hom ≫ _) = i.inv ≫ _
  rw [Iso.inv_hom_id_assoc]
  exact (bousfieldKanAugmentation_frame_naturality e.inv c).symm
end FrameWeightRealization

namespace ElementsCopower
variable (F : K ⥤ Type w) (B : K ⥤ SimplexCategory ⥤ C)
  (c : Cocone (ConstantWeightHom.degree K (frames F B) (SimplexCategory.mk 0)))

lemma realizationIso_hom_augmentation :
    (realizationIso F B (bousfieldKanWeight Kᵒᵖ)).hom ≫
      (FrameWeightRealization.functor F.Elements (Functor.Elements.π F ⋙ B)).map
        (ElementsUnderProjection.weightIso F).inv ≫
      FrameWeightRealization.bousfieldKanAugmentation (Functor.Elements.π F ⋙ B)
        (elementsZeroCocone F B c) =
      FrameWeightRealization.bousfieldKanAugmentation (frames F B) c := by
  let i := realizationIso F B (bousfieldKanWeight Kᵒᵖ) ≪≫
    (FrameWeightRealization.functor F.Elements (Functor.Elements.π F ⋙ B)).mapIso
      (ElementsUnderProjection.weightIso F).symm
  have h : i.inv ≫ FrameWeightRealization.bousfieldKanAugmentation (frames F B) c =
      FrameWeightRealization.bousfieldKanAugmentation (Functor.Elements.π F ⋙ B)
        (elementsZeroCocone F B c) := by
    change (_ ≫ _) ≫ _ = _
    rw [Category.assoc]
    exact realizationIso_inv_augmentation F B c
  rw [← Category.assoc]
  change i.hom ≫ _ = _
  rw [← h, Iso.hom_inv_id_assoc]
end ElementsCopower
end SerrePositivity.DiagramModel
