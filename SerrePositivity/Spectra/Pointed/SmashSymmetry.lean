module

public import SerrePositivity.Spectra.Pointed.Smash

/-!
# smash 積の交換同型

基点付き直積の二つの因子を交換し、その射を smash の普遍性で降ろす。
交換を二度行うと恒等射になること、および二つの変数での自然性を証明する。
この段階では結合子や hexagon を導入せず、閉対称モノイダル構造の交換射の基盤を与える。
直積と有限余極限だけを使い、モデル構造や追加の引用には依存しない。
-/

@[expose] public section

universe v u

noncomputable section

namespace SerrePositivity.PointedObject

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- 基点付き直積の因子を交換する射。 -/
def prodSwap (X Y : PointedObject C) : prod X Y ⟶ prod Y X :=
  prodLift (prodSnd X Y) (prodFst X Y)

@[reassoc (attr := simp)] lemma axisLeft_prodSwap (X Y : PointedObject C) :
    axisLeft X Y ≫ prodSwap X Y = axisRight Y X := by
  apply prod_hom_ext <;> simp [axisLeft, axisRight, prodSwap, Category.assoc]

@[reassoc (attr := simp)] lemma axisRight_prodSwap (X Y : PointedObject C) :
    axisRight X Y ≫ prodSwap X Y = axisLeft Y X := by
  apply prod_hom_ext <;> simp [axisLeft, axisRight, prodSwap, Category.assoc]

/-- 二回の交換は恒等射。 -/
@[simp] lemma prodSwap_comp (X Y : PointedObject C) :
    prodSwap X Y ≫ prodSwap Y X = 𝟙 (prod X Y) := by
  apply prod_hom_ext <;> simp [prodSwap, Category.assoc]

/-- 基点付き直積の交換同型。 -/
def prodSymmetry (X Y : PointedObject C) : prod X Y ≅ prod Y X where
  hom := prodSwap X Y
  inv := prodSwap Y X
  hom_inv_id := prodSwap_comp X Y
  inv_hom_id := prodSwap_comp Y X

instance prodSwap_isIso (X Y : PointedObject C) : IsIso (prodSwap X Y) :=
  (prodSymmetry X Y).isIso_hom

/-- 直積の交換は二つの変数で自然。 -/
@[reassoc] lemma prodSwap_naturality {X Y X' Y' : PointedObject C}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    prodMap f g ≫ prodSwap X' Y' = prodSwap X Y ≫ prodMap g f := by
  apply prod_hom_ext <;> simp [prodMap, prodSwap, Category.assoc]

variable [HasFiniteColimits C]

/-- 直積の交換を smash 積へ降ろした射。 -/
def smashSwap (X Y : PointedObject C) : smash X Y ⟶ smash Y X :=
  smashDesc (prodSwap X Y ≫ smashQuotient Y X) (by simp) (by simp)

@[reassoc (attr := simp)] lemma smashQuotient_swap (X Y : PointedObject C) :
    smashQuotient X Y ≫ smashSwap X Y = prodSwap X Y ≫ smashQuotient Y X :=
  smashQuotient_desc ..

/-- smash 積の交換を二回行うと恒等射になる。 -/
@[simp] lemma smashSwap_comp (X Y : PointedObject C) :
    smashSwap X Y ≫ smashSwap Y X = 𝟙 (smash X Y) := by
  apply smash_hom_ext
  simp [← Category.assoc (prodSwap X Y)]

/-- smash 積の交換同型。 -/
def smashSymmetry (X Y : PointedObject C) : smash X Y ≅ smash Y X where
  hom := smashSwap X Y
  inv := smashSwap Y X
  hom_inv_id := smashSwap_comp X Y
  inv_hom_id := smashSwap_comp Y X

/-- smash 積の交換射は二つの変数で自然。 -/
@[reassoc] lemma smashSwap_naturality {X Y X' Y' : PointedObject C}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    smashMap f g ≫ smashSwap X' Y' = smashSwap X Y ≫ smashMap g f := by
  apply smash_hom_ext
  simp only [smashQuotient_map_assoc, smashQuotient_swap_assoc,
    smashQuotient_swap, smashQuotient_map]
  rw [← Category.assoc, prodSwap_naturality, Category.assoc]

end SerrePositivity.PointedObject
