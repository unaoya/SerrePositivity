module

public import SerrePositivity.EInfinity.Hammock.LabelledColimitMap

/-!
# 元の fiber と余極限の交換の自然性

概要：元の自然変換による二つの fiber の写像と交換同値が可換する。
方針：元の共同全射な標準射で検査する。
規約：全ての写像は元の標準射に同じ代表を回収する。
使われ方：presheaf の各次数の同定を自然な同型に束ねる。
-/

@[expose] public section
universe uI vI u uB uC
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.LabelledColimit
open CategoryTheory CategoryTheory.Limits

variable {I : Type uI} [Category.{vI} I] {F G : I ⥤ Type u}
  (c : F.CoconeTypes.{uB}) (β : c.pt) (d : G.CoconeTypes.{uC}) (γ : d.pt)
  (σ : F ⟶ G) (h : ∀ i (x : F.obj i), c.ι i x = β → d.ι i (σ.app i x) = γ)
  [HasColimit F] [HasColimit G] [HasColimit (fiberDiagram c β)] [HasColimit (fiberDiagram d γ)]

lemma colimitFiberEquiv_natural (x : colimit (fiberDiagram c β)) :
    chosenFiberMap c β d γ σ h (colimitFiberEquiv c β x) =
      colimitFiberEquiv d γ (colimMap (fiberDiagramMap c β d γ σ h) x) := by
  obtain ⟨i, x, rfl⟩ := Types.jointly_surjective_of_isColimit
    (colimit.isColimit (fiberDiagram c β)) x
  have hm : colimMap (fiberDiagramMap c β d γ σ h) (colimit.ι (fiberDiagram c β) i x) =
      colimit.ι (fiberDiagram d γ) i ((fiberDiagramMap c β d γ σ h).app i x) :=
    ConcreteCategory.congr_hom (ι_colimMap (fiberDiagramMap c β d γ σ h) i) x
  change chosenFiberMap c β d γ σ h
    (colimitFiberEquiv c β (colimit.ι (fiberDiagram c β) i x)) =
      colimitFiberEquiv d γ
        (colimMap (fiberDiagramMap c β d γ σ h) (colimit.ι (fiberDiagram c β) i x))
  rw [hm, colimitFiberEquiv_apply_ι, colimitFiberEquiv_apply_ι, chosenFiberMap_ι]
  rfl

end SerrePositivity.EInfinity.Hammock.LabelledColimit
