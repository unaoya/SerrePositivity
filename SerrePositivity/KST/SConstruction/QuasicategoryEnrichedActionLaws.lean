module
public import SerrePositivity.KST.SConstruction.ClosedRightActionComposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCatSimplicial

/-! # 元の Quasi 値豊穣関手の実右作用の法則
概要：元の豊穣単位・合成等式は、uncurry した実全パラメータ作用の法則になる。
方針：閉構造の随伴の単位・合成公式を、同じ元の豊穣等式に適用する。
規約：頂点や h 圏へ制限しない。使われ方：実 core への作用の単位・合成の反映。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories

/-- 元の二つの関手族の合成を uncurry すると、同じ二回の実作用になる。 -/
lemma uncurry_tensor_internalComp {X Y Z P Q : SSet.{u}}
    (f : P ⟶ (ihom X).obj Y) (g : Q ⟶ (ihom Y).obj Z) :
    uncurry ((f ⊗ₘ g) ≫ MonoidalClosed.comp X Y Z) =
      (α_ X P Q).inv ≫ (uncurry f ⊗ₘ 𝟙 Q) ≫ uncurry g := by
  simpa only [curry_uncurry] using uncurry_curry_tensor_comp (uncurry f) (uncurry g)

variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
  (F : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{u})

/-- 元の豊穣恒等入力に対する実作用は、同じ元の値の恒等作用。 -/
lemma quasicategoryEnrichedAction_unit (X : C) :
    (𝟙 (F.obj X).obj ⊗ₘ eId SSet.{u} X) ≫ uncurry (F.map X X) =
      (ρ_ (F.obj X).obj).hom := by
  have h := congrArg
    (fun f : 𝟙_ SSet.{u} ⟶ (ihom (F.obj X).obj).obj (F.obj X).obj => uncurry f)
      (F.map_id X)
  rw [uncurry_natural_left] at h
  change _ = uncurry (MonoidalClosed.id (F.obj X).obj) at h
  rw [MonoidalClosed.id_eq, uncurry_curry] at h
  simpa only [id_tensorHom] using h

/-- 元の豊穣合成に対する実作用は、同じ元の値への二回の作用に厳密に一致。 -/
lemma quasicategoryEnrichedAction_comp (X Y Z : C) :
    (uncurry (F.map X Y) ⊗ₘ 𝟙 (Y ⟶[SSet.{u}] Z)) ≫ uncurry (F.map Y Z) =
      (α_ (F.obj X).obj (X ⟶[SSet.{u}] Y) (Y ⟶[SSet.{u}] Z)).hom ≫
        (𝟙 (F.obj X).obj ⊗ₘ eComp SSet.{u} X Y Z) ≫ uncurry (F.map X Z) := by
  have h := congrArg
    (fun f : (X ⟶[SSet.{u}] Y) ⊗ (Y ⟶[SSet.{u}] Z) ⟶
      (ihom (F.obj X).obj).obj (F.obj Z).obj => uncurry f) (F.map_comp X Y Z)
  change uncurry (eComp SSet.{u} X Y Z ≫ F.map X Z) =
    uncurry ((F.map X Y ⊗ₘ F.map Y Z) ≫ MonoidalClosed.comp _ _ _) at h
  rw [uncurry_natural_left, uncurry_tensor_internalComp] at h
  have hh := congrArg
    ((α_ (F.obj X).obj (X ⟶[SSet.{u}] Y) (Y ⟶[SSet.{u}] Z)).hom ≫ ·) h.symm
  simpa only [id_tensorHom, Category.assoc, Iso.hom_inv_id_assoc] using hh

end SerrePositivity.KST.SConstruction
