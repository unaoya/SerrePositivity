module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.LabelledColimitRelations

/-!
# 元の fiber の余極限から余極限の fiber への写像

概要：元の同じ代表を忘却して余極限の値の fiber へ送る。
方針：元の商の普遍性と元のラベルの自然性を使う。
規約：選ばれた代表を変更せず、標準射をそのまま回収する。
使われ方：任意の添字圏での fiber と余極限の交換。
-/

@[expose] public section
universe uI vI u uB
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.LabelledColimit
open CategoryTheory

variable {I : Type uI} [Category.{vI} I] {F : I ⥤ Type u}
  (c : F.CoconeTypes.{uB}) (β : c.pt)

def fiberForgetCocone : (fiberDiagram c β).CoconeTypes where
  pt := F.ColimitType
  ι i x := F.ιColimitType i x.val
  ι_naturality f := by
    funext x
    exact F.ιColimitType_map f x.val

def forgetQuotient : (fiberDiagram c β).ColimitType → F.ColimitType :=
  (fiberDiagram c β).descColimitType (fiberForgetCocone c β)

lemma forgetQuotient_label (x : (fiberDiagram c β).ColimitType) :
    F.descColimitType c (forgetQuotient c β x) = β := by
  refine Quot.inductionOn x ?_
  rintro ⟨i, x⟩
  exact x.property

def quotientFiberMap : (fiberDiagram c β).ColimitType →
    {z : F.ColimitType // F.descColimitType c z = β} :=
  fun x => ⟨forgetQuotient c β x, forgetQuotient_label c β x⟩

lemma quotientFiberMap_ι (i : I) (x : (fiberDiagram c β).obj i) :
    quotientFiberMap c β ((fiberDiagram c β).ιColimitType i x) =
      ⟨F.ιColimitType i x.val, x.property⟩ := rfl

end SerrePositivity.EInfinity.Hammock.LabelledColimit
