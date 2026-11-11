module

public import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# ラベル付き型値図式の値の fiber

概要：任意の型値図式の自然なラベルを固定した fiber の図式を作る。
方針：元の CoconeTypes のラベルの自然性を使う。
規約：添字圏の filtered 性を仮定しない。
使われ方：元の hammock の値の fiber と余極限の交換。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe uI vI u uB
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitFiber
open CategoryTheory

variable {I : Type uI} [Category.{vI} I] {F : I ⥤ Type u}
  (c : F.CoconeTypes.{uB}) (β : c.pt)

def fiberDiagram : I ⥤ Type u where
  obj i := {x : F.obj i // c.ι i x = β}
  map f := ↾fun x => ⟨F.map f x.val, (c.ι_naturality_apply f x.val).trans x.property⟩
  map_id i := by
    ext x
    exact ConcreteCategory.congr_hom (F.map_id i) x.val
  map_comp f g := by
    ext x
    exact ConcreteCategory.congr_hom (F.map_comp f g) x.val

def totalLabel (p : Σ i, F.obj i) : c.pt := c.ι p.1 p.2

lemma label_rel {p q : Σ i, F.obj i} (h : F.ColimitTypeRel p q) :
    totalLabel c p = totalLabel c q := by
  rcases p with ⟨i, x⟩
  rcases q with ⟨j, y⟩
  obtain ⟨f, hf⟩ := h
  change i ⟶ j at f
  change y = F.map f x at hf
  subst y
  exact (c.ι_naturality_apply f x).symm

lemma label_eqvGen {p q : Σ i, F.obj i} (h : Relation.EqvGen F.ColimitTypeRel p q) :
    totalLabel c p = totalLabel c q := by
  induction h with
  | rel p q h => exact label_rel c h
  | refl => rfl
  | symm p q h ih => exact ih.symm
  | trans p q r hp hq ihp ihq => exact ihp.trans ihq

def totalFiber (p : Σ i, F.obj i) (h : totalLabel c p = β) : Σ i, (fiberDiagram c β).obj i :=
  ⟨p.1, ⟨p.2, h⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledColimitFiber
