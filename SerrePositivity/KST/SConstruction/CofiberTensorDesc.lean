module
public import SerrePositivity.Spectra.Pointed.CofiberPushout
public import SerrePositivity.Spectra.PointedSimplicialSet.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-! # 二つの cofiber の smash からの射の降下
概要：両方の境界を零にする自由な基点を持つ対象の smash 上の射を、cofiber の smash へ降ろす。
方針：左右のテンソル積による cofiber の pushout の保存を二度使う。
規約：通常の点つき単体集合の smash。使われ方：反復 S の suspension 構造射。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial

/-- 概要：右の cofiber の pushout は左テンソルで保存される。
方針：閉モノイダルの左随伴の余極限保存を使う。
規約：全て点つき単体集合の射。使われ方：右側の境界の降下。 -/
lemma tensorCofiberRightSquare {A B : SSet.{u}} (g : A ⟶ B) (Y : PointedSimplicialSet.{u}) :
    IsPushout (Y ◁ PointedObject.adjoinFunctor.map g)
      (Y ◁ PointedObject.toPoint (PointedObject.adjoin A))
      (Y ◁ PointedObject.cofiberProjection g) (Y ◁ PointedObject.fromPoint (PointedObject.cofiber g)) :=
  PointedObject.map_cofiber_isPushout g (tensorLeft Y)

/-- 概要：左の cofiber の pushout は右テンソルで保存される。
方針：対称性と閉モノイダルの左随伴を使う。
規約：全て点つき単体集合の射。使われ方：左側の境界の降下。 -/
lemma tensorCofiberLeftSquare {A B : SSet.{u}} (f : A ⟶ B) (Y : PointedSimplicialSet.{u}) :
    IsPushout (PointedObject.adjoinFunctor.map f ▷ Y)
      (PointedObject.toPoint (PointedObject.adjoin A) ▷ Y)
      (PointedObject.cofiberProjection f ▷ Y) (PointedObject.fromPoint (PointedObject.cofiber f) ▷ Y) :=
  PointedObject.map_cofiber_isPushout f (tensorRight Y)

/-- 概要：右側の境界を零にする射を右 cofiber の smash へ降ろす。
方針：テンソルで写した pushout の普遍性。
規約：基点は厳密に保つ。使われ方：両側の境界の逐次降下。 -/
def tensorCofiberRightDesc {A B : SSet.{u}} (g : A ⟶ B) (Y Z : PointedSimplicialSet.{u})
    (h : Y ⊗ PointedObject.adjoin B ⟶ Z)
    (hg : (Y ◁ PointedObject.adjoinFunctor.map g) ≫ h = 0) :
    Y ⊗ PointedObject.cofiber g ⟶ Z :=
  (tensorCofiberRightSquare g Y).desc h 0 (by simpa using hg)

/-- 概要：右 cofiber への射影は降下前の射を回収する。
方針：pushout の降下の式。
規約：厳密等号。使われ方：左境界の零化の検証。 -/
lemma tensorCofiberRightDesc_quotient {A B : SSet.{u}} (g : A ⟶ B)
    (Y Z : PointedSimplicialSet.{u}) (h : Y ⊗ PointedObject.adjoin B ⟶ Z) (hg) :
    (Y ◁ PointedObject.cofiberProjection g) ≫ tensorCofiberRightDesc g Y Z h hg = h :=
  (tensorCofiberRightSquare g Y).inl_desc _ _ _

/-- 概要：右 cofiber の pushout の点の脚は降下後に零となる。
方針：pushout の第二脚の式。
規約：点との smash にも追加仮定なし。使われ方：左境界を写した式の比較。 -/
lemma tensorCofiberRightDesc_point {A B : SSet.{u}} (g : A ⟶ B)
    (Y Z : PointedSimplicialSet.{u}) (h : Y ⊗ PointedObject.adjoin B ⟶ Z) (hg) :
    (Y ◁ PointedObject.fromPoint (PointedObject.cofiber g)) ≫
      tensorCofiberRightDesc g Y Z h hg = 0 :=
  (tensorCofiberRightSquare g Y).inr_desc _ _ _

/-- 概要：左側の境界を零にする射を左 cofiber の smash へ降ろす。
方針：右テンソルで写した pushout の普遍性。
規約：通常の smash の射。使われ方：両側の境界の降下。 -/
def tensorCofiberLeftDesc {A B : SSet.{u}} (f : A ⟶ B) (Y Z : PointedSimplicialSet.{u})
    (h : PointedObject.adjoin B ⊗ Y ⟶ Z)
    (hf : (PointedObject.adjoinFunctor.map f ▷ Y) ≫ h = 0) :
    PointedObject.cofiber f ⊗ Y ⟶ Z :=
  (tensorCofiberLeftSquare f Y).desc h 0 (by simpa using hf)

/-- 概要：左 cofiber への射影は降下前の射を回収する。
方針：pushout の降下の式。
規約：厳密等号。使われ方：二つの商写像での構造射の回収。 -/
lemma tensorCofiberLeftDesc_quotient {A B : SSet.{u}} (f : A ⟶ B)
    (Y Z : PointedSimplicialSet.{u}) (h : PointedObject.adjoin B ⊗ Y ⟶ Z) (hf) :
    (PointedObject.cofiberProjection f ▷ Y) ≫ tensorCofiberLeftDesc f Y Z h hf = h :=
  (tensorCofiberLeftSquare f Y).inl_desc _ _ _

/-- 概要：右境界を潰した後も左境界の零化は保たれる。
方針：右 cofiber のテンソル pushout の二脚で等号を検出し、交換則を使う。
規約：両境界を零にする入力。使われ方：二段目の降下条件。 -/
lemma tensorCofiberRightDesc_left_zero {A B C D : SSet.{u}} (f : A ⟶ B) (g : C ⟶ D)
    (Z : PointedSimplicialSet.{u}) (h : PointedObject.adjoin B ⊗ PointedObject.adjoin D ⟶ Z)
    (hf : (PointedObject.adjoinFunctor.map f ▷ PointedObject.adjoin D) ≫ h = 0)
    (hg : (PointedObject.adjoin B ◁ PointedObject.adjoinFunctor.map g) ≫ h = 0) :
    (PointedObject.adjoinFunctor.map f ▷ PointedObject.cofiber g) ≫
      tensorCofiberRightDesc g (PointedObject.adjoin B) Z h hg = 0 := by
  let f' : PointedObject.adjoin A ⟶ PointedObject.adjoin B := PointedObject.adjoinFunctor.map f
  change (f' ▷ PointedObject.cofiber g) ≫ tensorCofiberRightDesc g _ Z h hg = 0
  apply (tensorCofiberRightSquare g (PointedObject.adjoin A)).hom_ext
  · rw [whisker_exchange_assoc, tensorCofiberRightDesc_quotient]
    exact hf.trans (comp_zero).symm
  · rw [whisker_exchange_assoc, tensorCofiberRightDesc_point]
    simp

/-- 概要：両側の境界を零にする射を二つの cofiber の smash へ降ろす。
方針：右側・左側の順でテンソル pushout から降ろす。
規約：追加の Kan 性を要求しない。使われ方：円と零境界商の smash からの構造射。 -/
def cofiberTensorDesc {A B C D : SSet.{u}} (f : A ⟶ B) (g : C ⟶ D)
    (Z : PointedSimplicialSet.{u}) (h : PointedObject.adjoin B ⊗ PointedObject.adjoin D ⟶ Z)
    (hf : (PointedObject.adjoinFunctor.map f ▷ PointedObject.adjoin D) ≫ h = 0)
    (hg : (PointedObject.adjoin B ◁ PointedObject.adjoinFunctor.map g) ≫ h = 0) :
    PointedObject.cofiber f ⊗ PointedObject.cofiber g ⟶ Z :=
  tensorCofiberLeftDesc f _ Z (tensorCofiberRightDesc g _ Z h hg)
    (tensorCofiberRightDesc_left_zero f g Z h hf hg)

/-- 概要：二つの商写像は cofiber の smash からの降下前の射を回収する。
方針：テンソル射を二つの whisker に分解し、各降下の回収式を使う。
規約：構造射を元の cylinder 上で照合する式。使われ方：構造写像の自然性と比較。 -/
lemma cofiberTensorDesc_quotient {A B C D : SSet.{u}} (f : A ⟶ B) (g : C ⟶ D)
    (Z : PointedSimplicialSet.{u}) (h : PointedObject.adjoin B ⊗ PointedObject.adjoin D ⟶ Z)
    (hf) (hg) :
    (PointedObject.cofiberProjection f ⊗ₘ PointedObject.cofiberProjection g) ≫
      cofiberTensorDesc f g Z h hf hg = h := by
  rw [tensorHom_def', Category.assoc, cofiberTensorDesc,
    tensorCofiberLeftDesc_quotient, tensorCofiberRightDesc_quotient]

end SerrePositivity.KST.SConstruction
