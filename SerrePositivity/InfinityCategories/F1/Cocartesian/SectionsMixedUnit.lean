module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.SectionsMixedCoreHom

/-!
概要：cocartesian fibration のパラメーターを固定すると、混合作用は元の section の前合成となる。
方針：同じ後合成の単位則を使い、core の豊穣単位から通常の前合成の射を回収する。
規約：定義域の制限は任意の底上の射。
使われ方：構成した同じ Cat∞ 値分類写像の fibration の頂点での値の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- 元の cocartesian 恒等関手の section への混合作用は、同じ定義域の前合成そのもの。 -/
lemma cocartesianSectionsMixedHom_unit {B : SSet.{u}} {a b : Over B}
    (f : a ⟶ b) (p : Over B) :
    cocartesianRelativeFunctorIdentity p ≫ cocartesianSectionsMixedHom f p p =
      curry' (kanCocartesianSectionsPre p.hom f) := by
  rw [cocartesianSectionsMixedHom, ← Category.assoc, cocartesianSectionsPostHom_id,
    ← curry'_id, curry'_ihom_map, Category.id_comp]

/-- 同じ混合作用は、core の豊穣単位を元の section の前合成の豊穣表示に写す。 -/
lemma cocartesianSectionsMixedCoreHom_unit {B : SSet.{u}} {a b : Over B}
    (f : a ⟶ b) (p : CocartesianFibrationCategory B) :
    eId SSet p ≫ cocartesianSectionsMixedCoreHom f p p =
      eHomEquiv SSet (show cocartesianSectionsQCatObject b p ⟶ cocartesianSectionsQCatObject a p
        from kanCocartesianSectionsPre p.val.hom f) := by
  apply (SSet.unitHomEquiv _).injective
  apply Subtype.ext
  exact congrArg (SSet.unitHomEquiv _) (cocartesianSectionsMixedHom_unit f p.val)

end SerrePositivity.InfinityCategories
