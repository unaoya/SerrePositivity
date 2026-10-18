module
public import SerrePositivity.KST.SConstruction.CofiberTensorDesc

/-! # cofiber の smash の射影による射の検出
概要：二つの cofiber の商射影の tensor はエピ射であり、そこへの引き戻しで射を検出できる。
方針：点への射のエピ性を pushout で移し、左右のテンソルの左随伴性で保つ。
規約：単射性や Kan 性は不要。使われ方：suspension の組み立ての自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet

/-- 概要：cofiber への自由な基点からの射影はエピ射。
方針：点への射がエピであることを pushout の脚へ移す。
規約：任意の単体集合の射。使われ方：smash の商射影による外延性。 -/
instance cofiberProjection_epi {A B : SSet.{u}} (f : A ⟶ B) :
    Epi (PointedObject.cofiberProjection f) := by
  have : Epi (PointedObject.toPoint (PointedObject.adjoin A)) := by
    constructor
    intro W h k _
    exact PointedObject.point_isZero.eq_of_src h k
  exact (PointedObject.cofiber_isPushout f).epi_inl_of_epi

/-- 概要：二つの cofiber の射影の tensor はエピ射。
方針：左右のテンソルでエピ性を保ち、合成に分解する。
規約：点つき単体集合の通常の smash。使われ方：降下した射の自然性の検出。 -/
instance cofiberTensorProjection_epi {A B C D : SSet.{u}} (f : A ⟶ B) (g : C ⟶ D) :
    Epi (PointedObject.cofiberProjection f ⊗ₘ PointedObject.cofiberProjection g) := by
  rw [tensorHom_def']
  have : Epi (PointedObject.adjoin B ◁ PointedObject.cofiberProjection g) :=
    (tensorLeft (PointedObject.adjoin B)).map_epi _
  have : Epi (PointedObject.cofiberProjection f ▷ PointedObject.cofiber g) :=
    (tensorRight (PointedObject.cofiber g)).map_epi _
  infer_instance

/-- 概要：cofiber の smash からの射は二つの商射影との合成で決まる。
方針：商射影の tensor のエピ性を使う。
規約：追加のモデル構造を使わない。使われ方：suspension の組み立ての比較。 -/
lemma cofiberTensor_hom_ext {A B C D : SSet.{u}} (f : A ⟶ B) (g : C ⟶ D)
    {Z : PointedSimplicialSet.{u}} (p q : PointedObject.cofiber f ⊗ PointedObject.cofiber g ⟶ Z)
    (h : (PointedObject.cofiberProjection f ⊗ₘ PointedObject.cofiberProjection g) ≫ p =
      (PointedObject.cofiberProjection f ⊗ₘ PointedObject.cofiberProjection g) ≫ q) : p = q :=
  (cancel_epi _).1 h

end SerrePositivity.KST.SConstruction
