module

public import SerrePositivity.Spectra.Pointed.Products

/-!
# 基点付き直積の結合同型と軸

直積の普遍性だけを使い、三変数の括弧を変える同型を構成する。
各変数を基点にする三つの射が、括弧の変更でどう移るかを証明する。
この比較により、三変数で reduced な射の普遍性を smash の両方の括弧へ適用できる。
smash の結合性やモノイダル構造を仮定しない。
-/

@[expose] public section

universe v u

noncomputable section

namespace SerrePositivity.PointedObject

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- 直積の三変数の括弧を左から右へ変える射。 -/
def prodAssocHom (X Y Z : PointedObject C) : prod (prod X Y) Z ⟶ prod X (prod Y Z) :=
  prodLift (prodFst (prod X Y) Z ≫ prodFst X Y)
    (prodLift (prodFst (prod X Y) Z ≫ prodSnd X Y) (prodSnd (prod X Y) Z))

/-- 直積の三変数の括弧を右から左へ変える射。 -/
def prodAssocInv (X Y Z : PointedObject C) : prod X (prod Y Z) ⟶ prod (prod X Y) Z :=
  prodLift (prodLift (prodFst X (prod Y Z)) (prodSnd X (prod Y Z) ≫ prodFst Y Z))
    (prodSnd X (prod Y Z) ≫ prodSnd Y Z)

/-- 基点付き直積の結合同型。 -/
def prodAssociator (X Y Z : PointedObject C) : prod (prod X Y) Z ≅ prod X (prod Y Z) where
  hom := prodAssocHom X Y Z
  inv := prodAssocInv X Y Z
  hom_inv_id := by
    apply prod_hom_ext
    · apply prod_hom_ext <;> simp [prodAssocHom, prodAssocInv, Category.assoc]
    · simp [prodAssocHom, prodAssocInv, Category.assoc]
  inv_hom_id := by
    apply prod_hom_ext
    · simp [prodAssocHom, prodAssocInv, Category.assoc]
    · apply prod_hom_ext <;> simp [prodAssocHom, prodAssocInv, Category.assoc]

@[reassoc (attr := simp)] lemma prodAssocHom_inv (X Y Z : PointedObject C) :
    prodAssocHom X Y Z ≫ prodAssocInv X Y Z = 𝟙 _ := (prodAssociator X Y Z).hom_inv_id

@[reassoc (attr := simp)] lemma prodAssocInv_hom (X Y Z : PointedObject C) :
    prodAssocInv X Y Z ≫ prodAssocHom X Y Z = 𝟙 _ := (prodAssociator X Y Z).inv_hom_id

@[reassoc (attr := simp)] lemma prodAssoc_first (X Y Z : PointedObject C) :
    prodMap (axisRight X Y) (𝟙 Z) ≫ prodAssocHom X Y Z = axisRight X (prod Y Z) := by
  apply prod_hom_ext
  · simp [prodAssocHom, prodMap, axisRight, Category.assoc]
  · apply prod_hom_ext <;> simp [prodAssocHom, prodMap, axisRight, Category.assoc]

@[reassoc (attr := simp)] lemma prodAssoc_second (X Y Z : PointedObject C) :
    prodMap (axisLeft X Y) (𝟙 Z) ≫ prodAssocHom X Y Z = prodMap (𝟙 X) (axisRight Y Z) := by
  apply prod_hom_ext
  · simp [prodAssocHom, prodMap, axisLeft, axisRight, Category.assoc]
  · apply prod_hom_ext <;> simp [prodAssocHom, prodMap, axisLeft, axisRight, Category.assoc]

@[reassoc (attr := simp)] lemma prodAssoc_third (X Y Z : PointedObject C) :
    axisLeft (prod X Y) Z ≫ prodAssocHom X Y Z = prodMap (𝟙 X) (axisLeft Y Z) := by
  apply prod_hom_ext
  · simp [prodAssocHom, prodMap, axisLeft, Category.assoc]
  · apply prod_hom_ext <;> simp [prodAssocHom, prodMap, axisLeft, Category.assoc]

@[reassoc (attr := simp)] lemma prodAssocInv_first (X Y Z : PointedObject C) :
    axisRight X (prod Y Z) ≫ prodAssocInv X Y Z = prodMap (axisRight X Y) (𝟙 Z) := by
  have h := congrArg (fun k ↦ k ≫ prodAssocInv X Y Z) (prodAssoc_first X Y Z)
  simpa only [Category.assoc, prodAssocHom_inv, Category.comp_id] using h.symm

@[reassoc (attr := simp)] lemma prodAssocInv_second (X Y Z : PointedObject C) :
    prodMap (𝟙 X) (axisRight Y Z) ≫ prodAssocInv X Y Z = prodMap (axisLeft X Y) (𝟙 Z) := by
  have h := congrArg (fun k ↦ k ≫ prodAssocInv X Y Z) (prodAssoc_second X Y Z)
  simpa only [Category.assoc, prodAssocHom_inv, Category.comp_id] using h.symm

@[reassoc (attr := simp)] lemma prodAssocInv_third (X Y Z : PointedObject C) :
    prodMap (𝟙 X) (axisLeft Y Z) ≫ prodAssocInv X Y Z = axisLeft (prod X Y) Z := by
  have h := congrArg (fun k ↦ k ≫ prodAssocInv X Y Z) (prodAssoc_third X Y Z)
  simpa only [Category.assoc, prodAssocHom_inv, Category.comp_id] using h.symm

/-- 直積の結合射は三つの変数で自然。 -/
@[reassoc] lemma prodAssoc_naturality {X Y Z X' Y' Z' : PointedObject C}
    (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    prodMap (prodMap f g) h ≫ prodAssocHom X' Y' Z' =
      prodAssocHom X Y Z ≫ prodMap f (prodMap g h) := by
  apply prod_hom_ext
  · simp [prodAssocHom, prodMap, Category.assoc]
  · apply prod_hom_ext <;> simp [prodAssocHom, prodMap, Category.assoc]

/-- 基点付き直積の結合射は pentagon を満たす。
smash の pentagon を標準射へ引き戻して証明する際の比較先となる。 -/
lemma prodAssoc_pentagon (W X Y Z : PointedObject C) :
    prodMap (prodAssocHom W X Y) (𝟙 Z) ≫ prodAssocHom W (prod X Y) Z ≫
      prodMap (𝟙 W) (prodAssocHom X Y Z) =
    prodAssocHom (prod W X) Y Z ≫ prodAssocHom W X (prod Y Z) := by
  apply prod_hom_ext
  · simp [prodAssocHom, prodMap, Category.assoc]
  · apply prod_hom_ext
    · simp [prodAssocHom, prodMap, Category.assoc]
    · apply prod_hom_ext <;> simp [prodAssocHom, prodMap, Category.assoc]

/-- 第一成分が零の直積写像は第二の軸を経由する。 -/
lemma prodMap_zero_left {X Y X' Y' : PointedObject C} (g : Y ⟶ Y') :
    prodMap (0 : X ⟶ X') g = prodSnd X Y ≫ g ≫ axisRight X' Y' := by
  apply prod_hom_ext <;> simp [prodMap, axisRight, Category.assoc]

/-- 第二成分が零の直積写像は第一の軸を経由する。 -/
lemma prodMap_zero_right {X Y X' Y' : PointedObject C} (f : X ⟶ X') :
    prodMap f (0 : Y ⟶ Y') = prodFst X Y ≫ f ≫ axisLeft X' Y' := by
  apply prod_hom_ext <;> simp [prodMap, axisLeft, Category.assoc]

end SerrePositivity.PointedObject
