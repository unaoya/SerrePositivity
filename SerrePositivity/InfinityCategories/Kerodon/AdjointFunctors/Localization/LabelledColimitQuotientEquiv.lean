module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitQuotientMap
public import Mathlib.Logic.Equiv.Basic

/-!
# 元の商余極限における fiber の全単射

概要：fiber の余極限は元の余極限の fiber と全単射になる。
方針：元の EqvGen の持ち上げと代表の共同全射性を使う。
規約：任意の添字圏と元の同じ商を使う。
使われ方：元の選ばれた型値余極限への同定の移送。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe uI vI u uB
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {I : Type uI} [Category.{vI} I] {F : I ⥤ Type u}
  (c : F.CoconeTypes.{uB}) (β : c.pt)

lemma quotientFiberMap_injective : Function.Injective (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.quotientFiberMap c β) := by
  intro x y
  refine Quot.inductionOn x ?_
  rintro ⟨i, x⟩
  refine Quot.inductionOn y ?_
  rintro ⟨j, y⟩ h
  apply Quot.eq.mpr
  have hb : F.ιColimitType i x.val = F.ιColimitType j y.val := congrArg Subtype.val h
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fiber_eqvGen c β ((F.ιColimitType_eq_iff x.val y.val).mp hb) x.property y.property

lemma quotientFiberMap_surjective : Function.Surjective (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.quotientFiberMap c β) := by
  rintro ⟨z, hz⟩
  obtain ⟨i, x, rfl⟩ := F.ιColimitType_jointly_surjective z
  exact ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitFiber.fiberDiagram c β).ιColimitType i ⟨x, hz⟩, rfl⟩

def quotientFiberEquiv : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitFiber.fiberDiagram c β).ColimitType ≃
    {z : F.ColimitType // F.descColimitType c z = β} :=
  Equiv.ofBijective (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.quotientFiberMap c β)
    ⟨quotientFiberMap_injective c β, quotientFiberMap_surjective c β⟩

lemma quotientFiberEquiv_apply_ι (i : I) (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitFiber.fiberDiagram c β).obj i) :
    quotientFiberEquiv c β ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitFiber.fiberDiagram c β).ιColimitType i x) =
      ⟨F.ιColimitType i x.val, x.property⟩ := rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
