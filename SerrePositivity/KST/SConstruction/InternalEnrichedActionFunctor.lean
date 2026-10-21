module
public import SerrePositivity.KST.SConstruction.InternalEnrichedActionLaws

/-! # 全作用の厳密な法則からの豊穣関手の構成
概要：元の実値と全作用を、同じ閉内部 Hom 値の厳密豊穣関手へ束ねる。
方針：元の単位・合成の法則を curry し、通常射の回収も同じ随伴で反映する。
規約：入力の Kan 性は不要。使われ方：同じ境界商の全 native 作用の包装。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
  (obj : C → SSet.{u}) (act : ∀ X Y, obj X ⊗ (X ⟶[SSet.{u}] Y) ⟶ obj Y)
  (hu : ∀ X, (𝟙 (obj X) ⊗ₘ eId SSet.{u} X) ≫ act X X = (ρ_ (obj X)).hom)
  (hc : ∀ X Y Z, (act X Y ⊗ₘ 𝟙 (Y ⟶[SSet.{u}] Z)) ≫ act Y Z =
    (α_ (obj X) (X ⟶[SSet.{u}] Y) (Y ⟶[SSet.{u}] Z)).hom ≫
      (𝟙 (obj X) ⊗ₘ eComp SSet.{u} X Y Z) ≫ act X Z)

/-- 同じ元の実値と全作用を保持する、閉内部 Hom 値の厳密豊穣関手。 -/
def internalEnrichedFunctorOfAction : EnrichedFunctor SSet.{u} C SSetInternalObject.{u} where
  obj X := ⟨obj X⟩
  map X Y := curry (act X Y)
  map_id X := by
    change eId SSet.{u} X ≫ curry (act X X) = MonoidalClosed.id (obj X)
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, MonoidalClosed.id_eq,
      uncurry_curry, ← id_tensorHom]
    exact hu X
  map_comp X Y Z := (rightActionCurry_comp _ _ _ _ (hc X Y Z)).symm

/-- 元の通常射の作用の回収を、同じ厳密豊穣関手の Hom 表示へ移す。 -/
lemma internalEnrichedFunctorOfAction_hom {X Y : C} (f : X ⟶ Y) (g : obj X ⟶ obj Y)
    (h : (𝟙 (obj X) ⊗ₘ eHomEquiv SSet.{u} f) ≫ act X Y = (ρ_ (obj X)).hom ≫ g) :
    eHomEquiv SSet.{u} f ≫ (internalEnrichedFunctorOfAction obj act hu hc).map X Y =
      curry' g := by
  change eHomEquiv SSet.{u} f ≫ curry (act X Y) = _
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_curry, curry', uncurry_curry]
  simpa only [id_tensorHom] using h

end SerrePositivity.KST.SConstruction
