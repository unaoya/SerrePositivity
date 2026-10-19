module
public import SerrePositivity.KST.SConstruction.BoundaryReduction

/-! # 部分複体を保つ同型の基点つき境界商への降下
概要：部分複体の像を対応させる単体集合の同型から、元の cofiber 商の同型を作る。
方針：cofiber の普遍性で順逆の射を降ろし、元の商射への引き戻しで逆律を示す。
規約：新しい商模型に置き換えない。使われ方：S₁ 内外交換の境界商の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet

/-- 部分複体を保つ写像が誘導する元の基点つき cofiber 商の射。 -/
def subcomplexCofiberMap {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex)
    (f : X ⟶ Y) (h : A.image f ≤ B) :
    PointedObject.cofiber A.ι ⟶ PointedObject.cofiber B.ι :=
  PointedObject.cofiberDesc A.ι _ (f ≫ PointedObject.cofiberQuotient B.ι) (by
    let g := Subcomplex.lift (A.ι ≫ f) (by simpa only [Subcomplex.image_eq_range] using h)
    have hg : g ≫ B.ι = A.ι ≫ f := Subcomplex.lift_ι _ _
    rw [← Category.assoc, ← hg, Category.assoc, PointedObject.cofiberQuotient_condition,
      comp_toUnit_assoc])

/-- 境界商から降ろした射は元の単体集合上の射を厳密に回収する。 -/
lemma subcomplexCofiberMap_quotient {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex)
    (f : X ⟶ Y) (h : A.image f ≤ B) :
    PointedObject.cofiberQuotient A.ι ≫ (subcomplexCofiberMap A B f h).right =
      f ≫ PointedObject.cofiberQuotient B.ι :=
  PointedObject.cofiberQuotient_desc _ _ _ _

/-- 部分複体の像を対応させる同型は、逆向きにもその部分複体を厳密に対応させる。 -/
lemma subcomplex_image_iso_inv {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex)
    (e : X ≅ Y) (h : A.image e.hom = B) : B.image e.inv = A := by
  rw [← h, ← Subcomplex.image_comp, e.hom_inv_id, Subcomplex.image_id]

/-- 部分複体を対応させる同型による、元の基点つき cofiber 商の同型。 -/
def subcomplexCofiberIso {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex)
    (e : X ≅ Y) (h : A.image e.hom = B) :
    PointedObject.cofiber A.ι ≅ PointedObject.cofiber B.ι where
  hom := subcomplexCofiberMap A B e.hom h.le
  inv := subcomplexCofiberMap B A e.inv (subcomplex_image_iso_inv A B e h).le
  hom_inv_id := by
    apply PointedObject.cofiber_hom_ext A.ι
    change PointedObject.cofiberQuotient A.ι ≫
      ((subcomplexCofiberMap A B e.hom h.le).right ≫
        (subcomplexCofiberMap B A e.inv (subcomplex_image_iso_inv A B e h).le).right) = _
    rw [← Category.assoc, subcomplexCofiberMap_quotient, Category.assoc,
      subcomplexCofiberMap_quotient, ← Category.assoc, e.hom_inv_id, Category.id_comp]
    rfl
  inv_hom_id := by
    apply PointedObject.cofiber_hom_ext B.ι
    change PointedObject.cofiberQuotient B.ι ≫
      ((subcomplexCofiberMap B A e.inv (subcomplex_image_iso_inv A B e h).le).right ≫
        (subcomplexCofiberMap A B e.hom h.le).right) = _
    rw [← Category.assoc, subcomplexCofiberMap_quotient, Category.assoc,
      subcomplexCofiberMap_quotient, ← Category.assoc, e.inv_hom_id, Category.id_comp]
    rfl

end SerrePositivity.KST.SConstruction
