module

public import SerrePositivity.Spectra.Pointed.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts

/-!
# 基点付き対象の直積

## 構成

基礎圏の直積に二つの基点を組として付ける。
射影と組み合わせる射を構成し、基点付き対象の圏での積の普遍性を証明する。
積への二つの軸は、一方を恒等射、他方を零射とする組み合わせとして定義する。

## 用途

基点付き単体的集合の直積と、smash 積で潰す wedge の射を構成する。
基礎圏の直積と、今後のsmashによるモノイダル積を区別する。
-/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.PointedObject

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- 基礎圏の直積に、基点の組を付けた対象。 -/
def prod (X Y : PointedObject C) : PointedObject C := Under.mk (lift X.hom Y.hom)

/-- 基点付き直積の第一射影。 -/
def prodFst (X Y : PointedObject C) : prod X Y ⟶ X :=
  Under.homMk (fst X.right Y.right) (by simp [prod])

/-- 基点付き直積の第二射影。 -/
def prodSnd (X Y : PointedObject C) : prod X Y ⟶ Y :=
  Under.homMk (snd X.right Y.right) (by simp [prod])

/-- 基点を保つ二つの射を組にする。 -/
def prodLift {W X Y : PointedObject C} (f : W ⟶ X) (g : W ⟶ Y) : W ⟶ prod X Y :=
  Under.homMk (lift f.right g.right) (by simp [prod, comp_lift])

@[reassoc (attr := simp)] lemma prodLift_fst {W X Y : PointedObject C}
    (f : W ⟶ X) (g : W ⟶ Y) : prodLift f g ≫ prodFst X Y = f := by
  apply Under.UnderMorphism.ext
  exact lift_fst _ _

@[reassoc (attr := simp)] lemma prodLift_snd {W X Y : PointedObject C}
    (f : W ⟶ X) (g : W ⟶ Y) : prodLift f g ≫ prodSnd X Y = g := by
  apply Under.UnderMorphism.ext
  exact lift_snd _ _

/-- 直積への射は二つの射影との合成で決まる。 -/
@[ext] lemma prod_hom_ext {W X Y : PointedObject C} (f g : W ⟶ prod X Y)
    (h₁ : f ≫ prodFst X Y = g ≫ prodFst X Y)
    (h₂ : f ≫ prodSnd X Y = g ≫ prodSnd X Y) : f = g := by
  apply Under.UnderMorphism.ext
  apply CartesianMonoidalCategory.hom_ext
  · exact congrArg Under.Hom.right h₁
  · exact congrArg Under.Hom.right h₂

/-- 明示的な直積と射影は、基点付き対象の圏の二項積を与える。 -/
def prodIsLimit (X Y : PointedObject C) : IsLimit (BinaryFan.mk (prodFst X Y) (prodSnd X Y)) :=
  BinaryFan.isLimitMk (fun s ↦ prodLift s.fst s.snd)
    (fun _ ↦ prodLift_fst _ _) (fun _ ↦ prodLift_snd _ _)
    (fun _ f h₁ h₂ ↦ prod_hom_ext f _ (h₁.trans (prodLift_fst _ _).symm)
      (h₂.trans (prodLift_snd _ _).symm))

/-- 明示的な積の普遍性から、二項積の存在を得る。 -/
instance : HasBinaryProducts (PointedObject C) := by
  let (X Y : PointedObject C) : HasLimit (pair X Y) := ⟨⟨_, prodIsLimit X Y⟩⟩
  exact hasBinaryProducts_of_hasLimit_pair _

/-- 二つの射が直積に誘導する射。 -/
def prodMap {X Y X' Y' : PointedObject C} (f : X ⟶ X') (g : Y ⟶ Y') :
    prod X Y ⟶ prod X' Y' := prodLift (prodFst X Y ≫ f) (prodSnd X Y ≫ g)

/-- 基点付き直積の写像は、基礎圏の直積の写像と一致する。 -/
@[simp] lemma prodMap_right {X Y X' Y' : PointedObject C} (f : X ⟶ X') (g : Y ⟶ Y') :
    (prodMap f g).right = f.right ⊗ₘ g.right := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [prodMap, prodLift, prodFst, prodSnd]

@[simp] lemma prodMap_id (X Y : PointedObject C) : prodMap (𝟙 X) (𝟙 Y) = 𝟙 (prod X Y) := by
  apply prod_hom_ext <;> simp [prodMap]

@[simp] lemma prodMap_comp {X Y X' Y' X'' Y'' : PointedObject C}
    (f : X ⟶ X') (g : Y ⟶ Y') (f' : X' ⟶ X'') (g' : Y' ⟶ Y'') :
    prodMap f g ≫ prodMap f' g' = prodMap (f ≫ f') (g ≫ g') := by
  apply prod_hom_ext <;> simp [prodMap, Category.assoc]

/-- 第一の対象を直積へ入れる軸。第二成分は基点で定数となる。 -/
def axisLeft (X Y : PointedObject C) : X ⟶ prod X Y := prodLift (𝟙 X) 0

/-- 第二の対象を直積へ入れる軸。第一成分は基点で定数となる。 -/
def axisRight (X Y : PointedObject C) : Y ⟶ prod X Y := prodLift 0 (𝟙 Y)

@[reassoc (attr := simp)] lemma axisLeft_prodMap {X Y X' Y' : PointedObject C}
    (f : X ⟶ X') (g : Y ⟶ Y') : axisLeft X Y ≫ prodMap f g = f ≫ axisLeft X' Y' := by
  apply prod_hom_ext <;> simp [axisLeft, prodMap, Category.assoc]

@[reassoc (attr := simp)] lemma axisRight_prodMap {X Y X' Y' : PointedObject C}
    (f : X ⟶ X') (g : Y ⟶ Y') : axisRight X Y ≫ prodMap f g = g ≫ axisRight X' Y' := by
  apply prod_hom_ext <;> simp [axisRight, prodMap, Category.assoc]

end SerrePositivity.PointedObject
