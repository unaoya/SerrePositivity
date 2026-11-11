module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitMap

/-!
# 元の fiber と余極限の交換の自然性

概要：元の自然変換による二つの fiber の写像と交換同値が可換する。
方針：元の共同全射な標準射で検査する。
規約：全ての写像は元の標準射に同じ代表を回収する。
使われ方：presheaf の各次数の同定を自然な同型に束ねる。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe uI vI u uB uC
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory CategoryTheory.Limits

variable {I : Type uI} [Category.{vI} I] {F G : I ⥤ Type u}
  (c : F.CoconeTypes.{uB}) (β : c.pt) (d : G.CoconeTypes.{uC}) (γ : d.pt)
  (σ : F ⟶ G) (h : ∀ i (x : F.obj i), c.ι i x = β → d.ι i (σ.app i x) = γ)
  [HasColimit F] [HasColimit G] [HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitFiber.fiberDiagram c β)] [HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitFiber.fiberDiagram d γ)]

lemma colimitFiberEquiv_natural (x : colimit (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitFiber.fiberDiagram c β)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.chosenFiberMap c β d γ σ h (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitFiberEquiv c β x) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitFiberEquiv d γ (colimMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fiberDiagramMap c β d γ σ h) x) := by
  obtain ⟨i, x, rfl⟩ := Types.jointly_surjective_of_isColimit
    (colimit.isColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitFiber.fiberDiagram c β)) x
  have hm : colimMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fiberDiagramMap c β d γ σ h) (colimit.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitFiber.fiberDiagram c β) i x) =
      colimit.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitFiber.fiberDiagram d γ) i ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fiberDiagramMap c β d γ σ h).app i x) :=
    ConcreteCategory.congr_hom (ι_colimMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fiberDiagramMap c β d γ σ h) i) x
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.chosenFiberMap c β d γ σ h
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitFiberEquiv c β (colimit.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitFiber.fiberDiagram c β) i x)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitFiberEquiv d γ
        (colimMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fiberDiagramMap c β d γ σ h) (colimit.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitFiber.fiberDiagram c β) i x))
  rw [hm, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitFiberEquiv_apply_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitFiberEquiv_apply_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.chosenFiberMap_ι]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
