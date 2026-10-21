module
public import SerrePositivity.KST.SConstruction.PointedEnrichedActionFunctor

/-! # basedHom の元の包含を使う標準点つき豊穣包装
概要：元の basedHom 包含後の作用法則から、同じ標準点つき厳密豊穣関手へ束ねる。
方針：包含を基礎単体集合への包装の射影から独立に指定し、一般の包装へ渡す。
規約：値と全入力族を変更しない。使われ方：大きな実 dg 入力の同じ商への豊穣化。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
  (obj : C → PointedSSetObject.{u})
  (act : ∀ X Y : C, (obj X).obj.right ⊗ (X ⟶[SSet.{u}] Y) ⟶ (obj Y).obj.right)
  (hu : ∀ X : C, (𝟙 (obj X).obj.right ⊗ₘ eId SSet.{u} X) ≫ act X X =
    (ρ_ (obj X).obj.right).hom)
  (hc : ∀ X Y Z : C, (act X Y ⊗ₘ 𝟙 (Y ⟶[SSet.{u}] Z)) ≫ act Y Z =
    (α_ (obj X).obj.right (X ⟶[SSet.{u}] Y) (Y ⟶[SSet.{u}] Z)).hom ≫
      (𝟙 (obj X).obj.right ⊗ₘ eComp SSet.{u} X Y Z) ≫ act X Z)
  (family : ∀ X Y : C, (X ⟶[SSet.{u}] Y) ⟶ (obj X ⟶[SSet.{u}] obj Y))
  (hi : ∀ X Y : C, family X Y ≫ PointedObject.basedHomι (obj X).obj (obj Y).obj =
    curry (act X Y))

/-- 元の basedHom 包含と同じ全作用から、標準点つき厳密豊穣関手を構成する。 -/
def pointedEnrichedFunctorOfBasedAction : EnrichedFunctor SSet.{u} C PointedSSetObject.{u} :=
  pointedEnrichedFunctorOfAction obj act hu hc family hi

/-- 全 basedHom 族の固定入力の作用から、同じ通常の点つき射を回収する。 -/
lemma pointedBasedFamily_hom {X Y : PointedSSetObject.{u}} {P : SSet.{u}}
    (p : 𝟙_ SSet.{u} ⟶ P) (a : X.obj.right ⊗ P ⟶ Y.obj.right)
    (f : P ⟶ (X ⟶[SSet.{u}] Y))
    (hf : f ≫ PointedObject.basedHomι X.obj Y.obj = curry a)
    (g : X ⟶ Y)
    (h : (𝟙 X.obj.right ⊗ₘ p) ≫ a =
      (ρ_ X.obj.right).hom ≫ (show X.obj ⟶ Y.obj from g).right) :
    p ≫ f = eHomEquiv SSet.{u} g := by
  apply (cancel_mono (PointedObject.basedHomι X.obj Y.obj)).mp
  have hg : eHomEquiv SSet.{u} g ≫ PointedObject.basedHomι X.obj Y.obj =
      curry' (show X.obj ⟶ Y.obj from g).right := pointedSSetObjectClosedForget_hom g
  apply uncurry_injective
  rw [Category.assoc, hf, uncurry_natural_left, uncurry_curry, hg, curry', uncurry_curry]
  simpa only [id_tensorHom] using h

end SerrePositivity.KST.SConstruction
