module
public import SerrePositivity.KST.SConstruction.CoaugmentedPointedSmash

/-! # 前向き smash 比較の両変数の厳密自然性
概要：写した値の smash と元の smash の像を結ぶ比較が、両因子の射と可換する。
方針：元の直積商で検出し、元の monoidal 比較と商の自然性に帰着する。
規約：比較の逆を使わない。使われ方：suspension 比較と元の構造写像の span。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open Functor.LaxMonoidal
variable (F : SSet.{u} ⥤ SSet.{u}) [F.Monoidal]
  (η : 𝟭 SSet.{u} ⟶ F) [NatTrans.IsMonoidal η]

/-- 標準点つき値の smash への、同じ元の二つの通常射の作用。 -/
def pointedSSetSmashMap {X Y X' Y' : PointedSSetObject.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    pointedSSetSmashObject X Y ⟶ pointedSSetSmashObject X' Y' :=
  (show X.obj ⟶ X'.obj from f) ⊗ₘ (show Y.obj ⟶ Y'.obj from g)

/-- 元の直積上で、乗法比較と元の smash 商の像は両変数について自然。 -/
lemma coaugmentedPointedSmash_product_naturality {X Y X' Y' : PointedSSetObject.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (F.map (show X.obj ⟶ X'.obj from f).right ⊗ₘ
      F.map (show Y.obj ⟶ Y'.obj from g).right) ≫ μ F X'.obj.right Y'.obj.right ≫
      F.map (PointedSimplicialSet.productToSmash X'.obj Y'.obj) =
    μ F X.obj.right Y.obj.right ≫
      F.map (PointedSimplicialSet.productToSmash X.obj Y.obj) ≫
      F.map (show (pointedSSetSmashObject X Y).obj ⟶
        (pointedSSetSmashObject X' Y').obj from pointedSSetSmashMap f g).right := by
  have h := PointedSimplicialSet.productToSmash_naturality
    (show X.obj ⟶ X'.obj from f) (show Y.obj ⟶ Y'.obj from g)
  erw [← Category.assoc, μ_natural, Category.assoc, ← F.map_comp, h, F.map_comp]
  rfl

/-- 元の smash 比較は、同じ写した両因子の通常射について厳密に自然。 -/
lemma coaugmentedPointedSmashMap_naturality {X Y X' Y' : PointedSSetObject.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    ((show (coaugmentedPointedObject F η X).obj ⟶
        (coaugmentedPointedObject F η X').obj from coaugmentedPointedMap F η f) ⊗ₘ
      (show (coaugmentedPointedObject F η Y).obj ⟶
        (coaugmentedPointedObject F η Y').obj from coaugmentedPointedMap F η g)) ≫
      coaugmentedPointedSmashMap F η X' Y' =
    coaugmentedPointedSmashMap F η X Y ≫
      (show (coaugmentedPointedObject F η (pointedSSetSmashObject X Y)).obj ⟶
        (coaugmentedPointedObject F η (pointedSSetSmashObject X' Y')).obj from
          coaugmentedPointedMap F η (pointedSSetSmashMap f g)) := by
  let f' : (coaugmentedPointedObject F η X).obj ⟶
      (coaugmentedPointedObject F η X').obj := coaugmentedPointedMap F η f
  let g' : (coaugmentedPointedObject F η Y).obj ⟶
      (coaugmentedPointedObject F η Y').obj := coaugmentedPointedMap F η g
  apply PointedObject.smash_hom_ext
  apply Under.UnderMorphism.ext
  have h := PointedSimplicialSet.productToSmash_naturality f' g'
  change PointedSimplicialSet.productToSmash _ _ ≫
      ((f' ⊗ₘ g').right ≫ (coaugmentedPointedSmashMap F η X' Y').right) =
    PointedSimplicialSet.productToSmash _ _ ≫
      ((coaugmentedPointedSmashMap F η X Y).right ≫
        F.map (show (pointedSSetSmashObject X Y).obj ⟶
          (pointedSSetSmashObject X' Y').obj from pointedSSetSmashMap f g).right)
  erw [← Category.assoc, ← h, Category.assoc, coaugmentedPointedSmashMap_quotient]
  erw [← Category.assoc (PointedSimplicialSet.productToSmash _ _),
    coaugmentedPointedSmashMap_quotient]
  exact coaugmentedPointedSmash_product_naturality F f g

end SerrePositivity.KST.SConstruction
