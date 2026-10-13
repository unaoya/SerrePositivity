module

public import SerrePositivity.CategoryTheory.FiniteBijection
public import SerrePositivity.CategoryTheory.FiniteBlockEquiv
public import Mathlib.CategoryTheory.Products.Basic

/-!
# 標準有限集合の直和

濃度の加法と、二つの全単射を隣接したブロックへ作用させる射を構成する。
convolution を直和に沿う左 Kan 拡張として定義するための二変数関手。
直和の結合子・単位・交換の登録は別に行う。
-/

@[expose] public section

namespace SerrePositivity.FiniteBijection

open CategoryTheory

/-- 二つの標準有限集合の直和。 -/
def sumObj (X Y : FiniteBijection) : FiniteBijection := of (card X + card Y)

/-- 直和上の射。 -/
def sumMap {X Y X' Y' : FiniteBijection} (f : X ⟶ X') (g : Y ⟶ Y') :
    sumObj X Y ⟶ sumObj X' Y' :=
  homOfEquiv (blockEquiv (equivOfHom f) (equivOfHom g))

@[simp] lemma sumMap_id (X Y : FiniteBijection) : sumMap (𝟙 X) (𝟙 Y) = 𝟙 (sumObj X Y) := by
  simp only [sumMap, equivOfHom_id, blockEquiv_refl]
  exact homOfEquiv_refl (sumObj X Y)

@[simp] lemma sumMap_comp {X Y X' Y' X'' Y'' : FiniteBijection}
    (f : X ⟶ X') (g : Y ⟶ Y') (f' : X' ⟶ X'') (g' : Y' ⟶ Y'') :
    sumMap f g ≫ sumMap f' g' = sumMap (f ≫ f') (g ≫ g') := by
  simp only [sumMap, equivOfHom_comp, ← blockEquiv_trans]
  exact (homOfEquiv_trans (X := sumObj X Y) (Y := sumObj X' Y')
    (Z := sumObj X'' Y'') _ _).symm

/-- 有限集合の直和の二変数関手。 -/
def sumFunctor : FiniteBijection × FiniteBijection ⥤ FiniteBijection where
  obj X := sumObj X.1 X.2
  map f := sumMap f.1 f.2
  map_id X := sumMap_id X.1 X.2
  map_comp f g := (sumMap_comp f.1 f.2 g.1 g.2).symm

end SerrePositivity.FiniteBijection
