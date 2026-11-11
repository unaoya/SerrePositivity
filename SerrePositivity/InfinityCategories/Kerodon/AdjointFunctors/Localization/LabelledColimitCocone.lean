module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitNaturality

/-!
# 任意の元の余極限余錐における fiber の普遍性

概要：元の余極限余錐のラベルの fiber も元の fiber の図式の余極限となる。
方針：元の商からの全単射とラベルの等式を制限する。
規約：余極限対象とラベルを別の選択で置き換えない。
使われ方：presheaf の元の各次数の余極限余錐。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe uI vI u uB uT
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitCocone
open CategoryTheory

variable {I : Type uI} [Category.{vI} I] {F : I ⥤ Type u}
  (c : F.CoconeTypes.{uB}) (β : c.pt) (t : F.CoconeTypes.{uT})
  (ℓ : t.pt → c.pt) (h : ∀ i x, ℓ (t.ι i x) = c.ι i x)

def fiberCocone : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitFiber.fiberDiagram c β).CoconeTypes where
  pt := {z : t.pt // ℓ z = β}
  ι i x := ⟨t.ι i x.val, (h i x.val).trans x.property⟩
  ι_naturality f := by
    funext x
    apply Subtype.ext
    exact t.ι_naturality_apply f x.val

include h in
lemma desc_label (z : F.ColimitType) : ℓ (F.descColimitType t z) = F.descColimitType c z := by
  refine Quot.inductionOn z ?_
  rintro ⟨i, x⟩
  exact h i x

def quotientCoconeFiberEquiv (ht : t.IsColimit) : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitFiber.fiberDiagram c β).ColimitType ≃
    {z : t.pt // ℓ z = β} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.quotientFiberEquiv c β).trans (Equiv.subtypeEquiv ht.equiv (fun z => by
    change (F.descColimitType c z = β) ↔ (ℓ (F.descColimitType t z) = β)
    rw [desc_label c t ℓ h]))

lemma fiberCocone_isColimit (ht : t.IsColimit) : (fiberCocone c β t ℓ h).IsColimit := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitFiber.fiberDiagram c β).isColimit_coconeTypes.of_equiv
    (c' := fiberCocone c β t ℓ h) (quotientCoconeFiberEquiv c β t ℓ h ht)
  intro i x
  rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitCocone
