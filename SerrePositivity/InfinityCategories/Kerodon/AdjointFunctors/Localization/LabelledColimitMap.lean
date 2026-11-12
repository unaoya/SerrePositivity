module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitEquiv

/-!
# ラベルの fiber を保つ図式間の写像

概要：元の自然変換が指定 fiber を保てば、元の余極限間の射も fiber を保つ。
方針：元の代表の共同全射性と標準射の回収を使う。
規約：必要なのは個々の余極限の存在だけである。
使われ方：全単体作用素に対する fiber 比較の自然性。

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

def fiberDiagramMap : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitFiber.fiberDiagram c β ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitFiber.fiberDiagram d γ where
  app i := ↾fun x => ⟨σ.app i x.val, h i x.val x.property⟩
  naturality i j f := by
    ext x
    apply Subtype.ext
    exact ConcreteCategory.congr_hom (σ.naturality f) x.val

variable [HasColimit F] [HasColimit G]

include h in
lemma colimit_map_label (x : colimit F) (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitLabel c x = β) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitLabel d (colimMap σ x) = γ := by
  obtain ⟨i, x, rfl⟩ := Types.jointly_surjective_of_isColimit (colimit.isColimit F) x
  have hm : colimMap σ (colimit.ι F i x) = colimit.ι G i (σ.app i x) :=
    ConcreteCategory.congr_hom (ι_colimMap σ i) x
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitLabel c (colimit.ι F i x) = β at hx
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitLabel d (colimMap σ (colimit.ι F i x)) = γ
  rw [hm, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitLabel_ι]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitLabel_ι] at hx
  exact h i x hx

def chosenFiberMap : {z : colimit F // _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitLabel c z = β} →
    {z : colimit G // _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitLabel d z = γ} :=
  fun x => ⟨colimMap σ x.val, colimit_map_label c β d γ σ h x.val x.property⟩

lemma chosenFiberMap_ι (i : I) (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitFiber.fiberDiagram c β).obj i) :
    chosenFiberMap c β d γ σ h
      ⟨colimit.ι F i x.val, (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitLabel_ι c i x.val).trans x.property⟩ =
        ⟨colimit.ι G i (σ.app i x.val),
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitLabel_ι d i _).trans (h i x.val x.property)⟩ := by
  apply Subtype.ext
  exact ConcreteCategory.congr_hom (ι_colimMap σ i) x.val

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
