module
public import SerrePositivity.KST.SConstruction.CoaugmentedPointedSmash

/-! # 元の smash 比較と monoidal な単位の厳密整合性
概要：元の両因子の単位から作った smash 射は、比較後に同じ smash 対象の単位を回収する。
方針：元の直積からの商射で検出し、単位の tensor 則と自然性を使う。
規約：比較の単射性は要求しない。使われ方：suspension 比較の単位条件。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open Functor.LaxMonoidal
variable (F : SSet.{u} ⥤ SSet.{u}) [F.Monoidal]
  (η : 𝟭 SSet.{u} ⟶ F) [NatTrans.IsMonoidal η]

/-- 元の単位の tensor 比較は、同じ元の直積対象の単位そのもの。 -/
lemma coaugmentedPointedSmash_unit_product (X Y : PointedSSetObject.{u}) :
    (η.app X.obj.right ⊗ₘ η.app Y.obj.right) ≫
      μ F X.obj.right Y.obj.right ≫ F.map (PointedSimplicialSet.productToSmash X.obj Y.obj) =
    PointedSimplicialSet.productToSmash X.obj Y.obj ≫
      η.app (pointedSSetSmashObject X Y).obj.right := by
  have ht := NatTrans.IsMonoidal.tensor (τ := η) X.obj.right Y.obj.right
  change 𝟙 _ ≫ η.app (X.obj.right ⊗ Y.obj.right) = _ at ht
  have hn := η.naturality (PointedSimplicialSet.productToSmash X.obj Y.obj)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun q => q ≫ F.map (PointedSimplicialSet.productToSmash X.obj Y.obj))
      ((Category.id_comp _).symm.trans ht).symm).trans hn.symm)

/-- 両因子の同じ点つき単位は、smash 比較の後で同じ smash 対象の単位を回収する。 -/
lemma coaugmentedPointedSmashMap_unit (X Y : PointedSSetObject.{u}) :
    ((show X.obj ⟶ (coaugmentedPointedObject F η X).obj from
      coaugmentedPointedUnit F η X) ⊗ₘ
      (show Y.obj ⟶ (coaugmentedPointedObject F η Y).obj from
        coaugmentedPointedUnit F η Y)) ≫ coaugmentedPointedSmashMap F η X Y =
    (show (pointedSSetSmashObject X Y).obj ⟶
      (coaugmentedPointedObject F η (pointedSSetSmashObject X Y)).obj from
        coaugmentedPointedUnit F η (pointedSSetSmashObject X Y)) := by
  let f : X.obj ⟶ (coaugmentedPointedObject F η X).obj := coaugmentedPointedUnit F η X
  let g : Y.obj ⟶ (coaugmentedPointedObject F η Y).obj := coaugmentedPointedUnit F η Y
  apply PointedObject.smash_hom_ext
  apply Under.UnderMorphism.ext
  have h := PointedSimplicialSet.productToSmash_naturality f g
  change PointedSimplicialSet.productToSmash X.obj Y.obj ≫
    ((f ⊗ₘ g) ≫
      coaugmentedPointedSmashMap F η X Y).right = _
  erw [Under.comp_right, ← Category.assoc, ← h, Category.assoc,
    coaugmentedPointedSmashMap_quotient]
  exact coaugmentedPointedSmash_unit_product F η X Y

end SerrePositivity.KST.SConstruction
