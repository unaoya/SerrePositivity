module
public import SerrePositivity.KST.SConstruction.LaxClosedFamilyMap
public import SerrePositivity.KST.SConstruction.SSetInternalObject
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-! # monoidal な単位を持つ関手の全単体的作用
概要：恒等からの monoidal な自然変換を使い、全元の内部 Hom を保持する。
方針：全 Hom の単位への像と lax 閉 Hom 比較を合成し、単位・合成を厳密に照合する。
規約：元の高次入力を離散化しない。使われ方：Ex∞ による厳密豊穣 Kan 置換。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open Functor.LaxMonoidal
variable (F : SSet.{u} ⥤ SSet.{u}) [F.LaxMonoidal]
  (η : 𝟭 SSet.{u} ⟶ F) [NatTrans.IsMonoidal η]

private lemma coaugmentation_unit : η.app (𝟙_ SSet.{u}) = ε F := by
  have h := NatTrans.IsMonoidal.unit (τ := η)
  change 𝟙 _ ≫ η.app (𝟙_ SSet.{u}) = ε F at h
  exact (Category.id_comp _).symm.trans h

private lemma coaugmentation_tensor (X Y : SSet.{u}) :
    η.app (X ⊗ Y) = (η.app X ⊗ₘ η.app Y) ≫ μ F X Y := by
  have h := NatTrans.IsMonoidal.tensor (τ := η) X Y
  change 𝟙 _ ≫ η.app (X ⊗ Y) = _ at h
  exact (Category.id_comp _).symm.trans h

/-- 同じ全内部 Hom を単位で写してから、元の lax 閉 Hom 比較を適用する。 -/
def coaugmentedClosedFamilyMap (X Y : SSet.{u}) :
    (ihom X).obj Y ⟶ (ihom (F.obj X)).obj (F.obj Y) :=
  η.app ((ihom X).obj Y) ≫ laxClosedFamilyMap F X Y

/-- 元の通常射では、同じ写した通常射を全 Hom 作用から回収する。 -/
lemma coaugmentedClosedFamilyMap_hom {X Y : SSet.{u}} (f : X ⟶ Y) :
    curry' f ≫ coaugmentedClosedFamilyMap F η X Y = curry' (F.map f) := by
  have hn := η.naturality (curry' f)
  change curry' f ≫ η.app ((ihom X).obj Y) =
    η.app (𝟙_ SSet.{u}) ≫ F.map (curry' f) at hn
  rw [coaugmentedClosedFamilyMap, ← Category.assoc, hn,
    coaugmentation_unit F η]
  exact laxClosedFamilyMap_hom F f

/-- 全 Hom 作用は元の閉 Hom の恒等射を厳密に保つ。 -/
lemma coaugmentedClosedFamilyMap_id (X : SSet.{u}) :
    MonoidalClosed.id X ≫ coaugmentedClosedFamilyMap F η X X =
      MonoidalClosed.id (F.obj X) := by
  simpa only [curry'_id, F.map_id] using coaugmentedClosedFamilyMap_hom F η (𝟙 X)

/-- 全 Hom 作用は元の全内部 Hom の合成を厳密に保つ。 -/
lemma coaugmentedClosedFamilyMap_comp (X Y Z : SSet.{u}) :
    MonoidalClosed.comp X Y Z ≫ coaugmentedClosedFamilyMap F η X Z =
      (coaugmentedClosedFamilyMap F η X Y ⊗ₘ coaugmentedClosedFamilyMap F η Y Z) ≫
        MonoidalClosed.comp (F.obj X) (F.obj Y) (F.obj Z) := by
  have hn := η.naturality (MonoidalClosed.comp X Y Z)
  change MonoidalClosed.comp X Y Z ≫ η.app ((ihom X).obj Z) =
    η.app (((ihom X).obj Y) ⊗ ((ihom Y).obj Z)) ≫
      F.map (MonoidalClosed.comp X Y Z) at hn
  rw [coaugmentedClosedFamilyMap, ← Category.assoc, hn,
    coaugmentation_tensor F η]
  rw [Category.assoc, Category.assoc,
    ← Category.assoc (μ F _ _) (F.map (MonoidalClosed.comp X Y Z))
      (laxClosedFamilyMap F X Z), laxClosedFamilyMap_comp]
  rw [← Category.assoc, tensorHom_comp_tensorHom]
  rfl

/-- monoidal な単位を持つ関手は、元の全 Hom を保つ厳密単体的豊穣関手を与える。 -/
def coaugmentedClosedEnrichedFunctor :
    EnrichedFunctor SSet.{u} SSetInternalObject.{u} SSetInternalObject.{u} where
  obj X := ⟨F.obj X.obj⟩
  map X Y := coaugmentedClosedFamilyMap F η X.obj Y.obj
  map_id X := coaugmentedClosedFamilyMap_id F η X.obj
  map_comp X Y Z := coaugmentedClosedFamilyMap_comp F η X.obj Y.obj Z.obj

end SerrePositivity.KST.SConstruction
