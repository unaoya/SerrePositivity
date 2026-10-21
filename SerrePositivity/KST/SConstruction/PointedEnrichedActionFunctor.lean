module
public import SerrePositivity.KST.SConstruction.PointedSSetObject
public import SerrePositivity.KST.SConstruction.InternalEnrichedActionFunctor

/-! # 元の全作用の標準点つき豊穣への包装
概要：元の全 basedHom 族を、同じ点つき値の標準厳密豊穣関手に束ねる。
方針：閉内部 Hom への包含の単射性で、元の全作用の単位・合成を反映する。
規約：basedHom の標準の合成を使う。使われ方：元の境界商と点つき Kan 置換。
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
  (hi : ∀ X Y : C, family X Y ≫ pointedSSetObjectClosedForget.map (obj X) (obj Y) =
    curry (act X Y))

/-- 同じ実点つき値と全 basedHom 族を持つ、標準の厳密単体的豊穣関手。 -/
def pointedEnrichedFunctorOfAction : EnrichedFunctor SSet.{u} C PointedSSetObject.{u} where
  obj := obj
  map := family
  map_id X := by
    apply (cancel_mono (PointedObject.basedHomι (obj X).obj (obj X).obj)).mp
    have h := (internalEnrichedFunctorOfAction
      (fun X => (obj X).obj.right) act hu hc).map_id X
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun q => eId SSet.{u} X ≫ q) (hi X X)).trans
        (h.trans (pointedSSetObjectClosedForget.map_id (obj X)).symm))
  map_comp X Y Z := by
    apply (cancel_mono (PointedObject.basedHomι (obj X).obj (obj Z).obj)).mp
    change (eComp SSet.{u} X Y Z ≫ family X Z) ≫
      pointedSSetObjectClosedForget.map (obj X) (obj Z) =
        ((family X Y ⊗ₘ family Y Z) ≫ eComp SSet.{u} (obj X) (obj Y) (obj Z)) ≫
          pointedSSetObjectClosedForget.map (obj X) (obj Z)
    rw [Category.assoc, hi, Category.assoc, pointedSSetObjectClosedForget.map_comp,
      ← Category.assoc, tensorHom_comp_tensorHom, hi, hi]
    exact (internalEnrichedFunctorOfAction (fun X => (obj X).obj.right) act hu hc).map_comp
      X Y Z

/-- 元の通常射の作用を回収すれば、同じ元の点つき射の標準豊穣表示を回収する。 -/
lemma pointedEnrichedFunctorOfAction_hom {X Y : C} (f : X ⟶ Y)
    (g : obj X ⟶ obj Y)
    (h : (𝟙 (obj X).obj.right ⊗ₘ eHomEquiv SSet.{u} f) ≫ act X Y =
      (ρ_ (obj X).obj.right).hom ≫ (show (obj X).obj ⟶ (obj Y).obj from g).right) :
    eHomEquiv SSet.{u} f ≫ (pointedEnrichedFunctorOfAction obj act hu hc family hi).map X Y =
      eHomEquiv SSet.{u} g := by
  apply (cancel_mono (PointedObject.basedHomι (obj X).obj (obj Y).obj)).mp
  have hh := internalEnrichedFunctorOfAction_hom
    (fun X => (obj X).obj.right) act hu hc f _ h
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun q => eHomEquiv SSet.{u} f ≫ q) (hi X Y)).trans
      (hh.trans (pointedSSetObjectClosedForget_hom g).symm))

end SerrePositivity.KST.SConstruction
