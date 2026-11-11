module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitQuotientEquiv

/-!
# 元の選ばれた型値余極限と fiber の交換

概要：fiber の元の余極限を元の余極限の fiber と同定する。
方針：商による同定を元の余極限の標準同値で移す。
規約：必要なのは二つの余極限の存在だけで、filtered 性は不要。
使われ方：presheaf の各次数における fiber の余極限。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe uI vI u uB
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory CategoryTheory.Limits

variable {I : Type uI} [Category.{vI} I] {F : I ⥤ Type u}
  (c : F.CoconeTypes.{uB}) (β : c.pt) [HasColimit F]

def colimitLabel (z : colimit F) : c.pt :=
  F.descColimitType c (Types.colimitEquivColimitType F z)

lemma colimitLabel_ι (i : I) (x : F.obj i) :
    colimitLabel c (colimit.ι F i x) = c.ι i x := by
  dsimp only [colimitLabel]
  rw [Types.colimitEquivColimitType_apply]
  rfl

def quotientToChosenFiberEquiv : {z : F.ColimitType // F.descColimitType c z = β} ≃
    {z : colimit F // colimitLabel c z = β} :=
  Equiv.subtypeEquiv (Types.colimitEquivColimitType F).symm (fun z => by
    change (F.descColimitType c z = β) ↔
      (F.descColimitType c (Types.colimitEquivColimitType F
        ((Types.colimitEquivColimitType F).symm z)) = β)
    rw [Equiv.apply_symm_apply])

variable [HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitFiber.fiberDiagram c β)]

def colimitFiberEquiv : colimit (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitFiber.fiberDiagram c β) ≃ {z : colimit F // colimitLabel c z = β} :=
  (Types.colimitEquivColimitType (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitFiber.fiberDiagram c β)).trans
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.quotientFiberEquiv c β).trans (quotientToChosenFiberEquiv c β))

lemma colimitFiberEquiv_apply_ι (i : I) (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitFiber.fiberDiagram c β).obj i) :
    colimitFiberEquiv c β (colimit.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitFiber.fiberDiagram c β) i x) =
      ⟨colimit.ι F i x.val, (colimitLabel_ι c i x.val).trans x.property⟩ := by
  apply Subtype.ext
  change (Types.colimitEquivColimitType F).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forgetQuotient c β (Types.colimitEquivColimitType (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitFiber.fiberDiagram c β)
      (colimit.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitFiber.fiberDiagram c β) i x))) = colimit.ι F i x.val
  rw [Types.colimitEquivColimitType_apply]
  exact Types.colimitEquivColimitType_symm_apply F i x.val

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
