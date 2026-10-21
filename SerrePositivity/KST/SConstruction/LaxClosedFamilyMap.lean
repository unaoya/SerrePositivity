module
public import SerrePositivity.KST.SConstruction.QuasicategoryEnrichedActionLaws
public import Mathlib.CategoryTheory.Monoidal.Functor

/-! # lax monoidal 関手の全内部 Hom 比較
概要：lax monoidal な単体集合値関手から、元の全閉内部 Hom への比較を構成する。
方針：tensor 比較の後で元の評価を写して curry し、単位と合成を随伴で照合する。
規約：比較の可逆性は要求しない。使われ方：点つき忘却と Ex∞ の厳密豊穣化。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open Functor.LaxMonoidal
variable {C : Type v} [Category.{w} C] [MonoidalCategory C] [MonoidalClosed C]
  (F : C ⥤ SSet.{u}) [F.LaxMonoidal]

/-- 元の評価と lax tensor 比較を保持する、全閉内部 Hom の実比較。 -/
def laxClosedFamilyMap (X Y : C) :
    F.obj ((ihom X).obj Y) ⟶ (ihom (F.obj X)).obj (F.obj Y) :=
  curry (μ F X ((ihom X).obj Y) ≫ F.map ((ihom.ev X).app Y))

/-- 元の通常射の閉 Hom 表示は、同じ写した射の閉 Hom 表示を回収する。 -/
lemma laxClosedFamilyMap_hom {X Y : C} (f : X ⟶ Y) :
    (ε F ≫ F.map (curry' f)) ≫ laxClosedFamilyMap F X Y = curry' (F.map f) := by
  apply uncurry_injective
  change uncurry ((ε F ≫ F.map (curry' f)) ≫
    curry (μ F X ((ihom X).obj Y) ≫ F.map ((ihom.ev X).app Y))) =
      uncurry (curry ((ρ_ (F.obj X)).hom ≫ F.map f))
  rw [uncurry_natural_left, uncurry_curry, uncurry_curry,
    whiskerLeft_comp, Category.assoc, μ_natural_right_assoc, ← F.map_comp,
    whiskerLeft_curry'_ihom_ev_app, F.map_comp, ← right_unitality_assoc]

/-- 元の閉 Hom の恒等射は、同じ写した実値の恒等射を回収する。 -/
lemma laxClosedFamilyMap_id (X : C) :
    (ε F ≫ F.map (MonoidalClosed.id X)) ≫ laxClosedFamilyMap F X X =
      MonoidalClosed.id (F.obj X) := by
  simpa only [curry'_id, F.map_id] using laxClosedFamilyMap_hom F (𝟙 X)

private lemma closed_comp_evaluation (X Y Z : C) :
    (X ◁ MonoidalClosed.comp X Y Z) ≫ (ihom.ev X).app Z = compTranspose X Y Z := by
  rw [← uncurry_eq, comp_eq, uncurry_curry]

/-- 元の全閉 Hom の合成は、比較後の同じ全内部 Hom の合成と厳密に一致。 -/
lemma laxClosedFamilyMap_comp (X Y Z : C) :
    (μ F ((ihom X).obj Y) ((ihom Y).obj Z) ≫ F.map (MonoidalClosed.comp X Y Z)) ≫
      laxClosedFamilyMap F X Z =
        (laxClosedFamilyMap F X Y ⊗ₘ laxClosedFamilyMap F Y Z) ≫
          MonoidalClosed.comp (F.obj X) (F.obj Y) (F.obj Z) := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_tensor_internalComp]
  simp only [laxClosedFamilyMap, uncurry_curry]
  rw [whiskerLeft_comp, Category.assoc, μ_natural_right_assoc, ← F.map_comp,
    closed_comp_evaluation, compTranspose_eq, F.map_comp, F.map_comp,
    associativity_inv_assoc, ← μ_natural_left_assoc]
  simp only [tensorHom_id, comp_whiskerRight, Category.assoc]
  rfl

end SerrePositivity.KST.SConstruction
