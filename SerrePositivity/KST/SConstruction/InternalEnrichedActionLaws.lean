module
public import SerrePositivity.KST.SConstruction.SSetInternalObject
public import SerrePositivity.KST.SConstruction.QuasicategoryEnrichedActionLaws

/-! # 閉内部 Hom 値の元の全作用の法則
概要：任意の実単体集合値の厳密豊穣関手から、全作用の単位・合成を回収する。
方針：元の豊穣等式を uncurry し、閉構造の単位・合成を使う。
規約：値の Kan 性は要求しない。使われ方：境界の商へ降ろす元の実現作用。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
  (F : EnrichedFunctor SSet.{u} C SSetInternalObject.{u})

/-- 元の豊穣恒等入力に対する作用は、同じ実値の恒等作用。 -/
lemma internalEnrichedAction_unit (X : C) :
    (𝟙 (F.obj X).obj ⊗ₘ eId SSet.{u} X) ≫ uncurry (F.map X X) =
      (ρ_ (F.obj X).obj).hom := by
  have h := congrArg
    (fun q : 𝟙_ SSet.{u} ⟶ (ihom (F.obj X).obj).obj (F.obj X).obj => uncurry q)
      (F.map_id X)
  rw [uncurry_natural_left] at h
  change _ = uncurry (MonoidalClosed.id (F.obj X).obj) at h
  rw [MonoidalClosed.id_eq, uncurry_curry] at h
  simpa only [id_tensorHom] using h

/-- 二回の元の全作用は、同じ豊穣合成による作用と厳密に一致。 -/
lemma internalEnrichedAction_comp (X Y Z : C) :
    (uncurry (F.map X Y) ⊗ₘ 𝟙 (Y ⟶[SSet.{u}] Z)) ≫ uncurry (F.map Y Z) =
      (α_ (F.obj X).obj (X ⟶[SSet.{u}] Y) (Y ⟶[SSet.{u}] Z)).hom ≫
        (𝟙 (F.obj X).obj ⊗ₘ eComp SSet.{u} X Y Z) ≫ uncurry (F.map X Z) := by
  have h := congrArg
    (fun q : (X ⟶[SSet.{u}] Y) ⊗ (Y ⟶[SSet.{u}] Z) ⟶
      (ihom (F.obj X).obj).obj (F.obj Z).obj => uncurry q) (F.map_comp X Y Z)
  change uncurry (eComp SSet.{u} X Y Z ≫ F.map X Z) =
    uncurry ((F.map X Y ⊗ₘ F.map Y Z) ≫ MonoidalClosed.comp _ _ _) at h
  rw [uncurry_natural_left, uncurry_tensor_internalComp] at h
  have hh := congrArg
    ((α_ (F.obj X).obj (X ⟶[SSet.{u}] Y) (Y ⟶[SSet.{u}] Z)).hom ≫ ·) h.symm
  simpa only [id_tensorHom, Category.assoc, Iso.hom_inv_id_assoc] using hh

/-- 通常射の元の像を回収する全作用の式。 -/
lemma internalEnrichedAction_hom {X Y : C} (f : X ⟶ Y)
    (g : (F.obj X).obj ⟶ (F.obj Y).obj)
    (h : eHomEquiv SSet.{u} f ≫ F.map X Y = curry' g) :
    (𝟙 (F.obj X).obj ⊗ₘ eHomEquiv SSet.{u} f) ≫ uncurry (F.map X Y) =
      (ρ_ (F.obj X).obj).hom ≫ g := by
  have hh := congrArg
    (fun q : 𝟙_ SSet.{u} ⟶ (ihom (F.obj X).obj).obj (F.obj Y).obj => uncurry q) h
  rw [uncurry_natural_left, curry', uncurry_curry] at hh
  simpa only [id_tensorHom] using hh

end SerrePositivity.KST.SConstruction
