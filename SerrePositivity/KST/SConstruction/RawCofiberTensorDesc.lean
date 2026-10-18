module
public import SerrePositivity.KST.SConstruction.CofiberTensorDesc
public import SerrePositivity.Spectra.Pointed.AdjoinBasepointProduct

/-! # 両境界を基点へ送る通常の写像の smash への降下
概要：通常の積上の写像が両境界を基点へ送るなら、二つの cofiber の smash から写せる。
方針：自由な基点の追加と積の比較を使い、点つきの二段の降下へ渡す。
規約：ホモトピー論の仮定なし。使われ方：反復 S の実際の suspension からの写像。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial

/-- 概要：通常の積からの射を自由な基点を持つ対象の smash 上の射へ移す。
方針：基点追加と smash の比較同型、基点追加の随伴の Hom 同値。
規約：元の対象に基点は要求しない。使われ方：cofiber の smash への降下。 -/
def adjoinTensorMap {A B : SSet.{u}} (Z : PointedSimplicialSet.{u}) (h : A ⊗ B ⟶ Z.right) :
    PointedObject.adjoin A ⊗ PointedObject.adjoin B ⟶ Z :=
  PointedObject.adjoinSmashHom A B ≫ (PointedObject.adjoinHomEquiv (A ⊗ B) Z).symm h

/-- 概要：自由な基点を加えた積上の射は両入力の射について自然。
方針：基点追加と smash の比較の自然性と余積の普遍性を使う。
規約：厳密等号。使われ方：境界の条件の点つき表示。 -/
lemma adjoinTensorMap_precomp {A B C D : SSet.{u}} (f : A ⟶ B) (g : C ⟶ D)
    (Z : PointedSimplicialSet.{u}) (h : B ⊗ D ⟶ Z.right) :
    (PointedObject.adjoinFunctor.map f ⊗ₘ PointedObject.adjoinFunctor.map g) ≫
      adjoinTensorMap Z h = adjoinTensorMap Z ((f ⊗ₘ g) ≫ h) := by
  change PointedObject.smashMap (PointedObject.adjoinFunctor.map f)
      (PointedObject.adjoinFunctor.map g) ≫
      (PointedObject.adjoinSmashHom B D ≫ _) = PointedObject.adjoinSmashHom A C ≫ _
  rw [← Category.assoc, PointedObject.adjoinSmashHom_naturality, Category.assoc]
  congr 1
  apply (PointedObject.adjoinHomEquiv (A ⊗ C) Z).injective
  simp [PointedObject.adjoinHomEquiv, PointedObject.adjoinFunctor]

/-- 概要：基点で定数の通常の射は、基点を加えた smash 上では零射。
方針：基点追加の Hom 同値で零射の底を計算する。
規約：定数射は終対象経由で書く。使われ方：境界の零化。 -/
lemma adjoinTensorMap_zero {A B : SSet.{u}} (Z : PointedSimplicialSet.{u})
    (h : A ⊗ B ⟶ Z.right)
    (hh : h = CartesianMonoidalCategory.toUnit (A ⊗ B) ≫ Z.hom) :
    adjoinTensorMap Z h = 0 := by
  have hz : (PointedObject.adjoinHomEquiv (A ⊗ B) Z).symm h = 0 := by
    apply (PointedObject.adjoinHomEquiv (A ⊗ B) Z).injective
    rw [Equiv.apply_symm_apply]
    change h = coprod.inl ≫ (0 : PointedObject.adjoin (A ⊗ B) ⟶ Z).right
    rw [PointedObject.zero_right]
    change h = (coprod.inl : A ⊗ B ⟶ (A ⊗ B) ⨿ (𝟙_ SSet.{u})) ≫
      CartesianMonoidalCategory.toUnit ((A ⊗ B) ⨿ (𝟙_ SSet.{u})) ≫ Z.hom
    rw [CartesianMonoidalCategory.comp_toUnit_assoc]
    exact hh
  unfold adjoinTensorMap
  rw [hz, comp_zero]

/-- 概要：通常の左境界を基点へ送る条件は点つきの左境界の零化を与える。
方針：基点追加の自然性と定数射の零化を使う。
規約：全高次単体の等号を入力とする。使われ方：左 cofiber の降下条件。 -/
lemma adjoinTensorMap_left_zero {A B D : SSet.{u}} (f : A ⟶ B)
    (Z : PointedSimplicialSet.{u}) (h : B ⊗ D ⟶ Z.right)
    (hf : (f ▷ D) ≫ h = CartesianMonoidalCategory.toUnit (A ⊗ D) ≫ Z.hom) :
    (PointedObject.adjoinFunctor.map f ▷ PointedObject.adjoin D) ≫ adjoinTensorMap Z h = 0 := by
  have hp := adjoinTensorMap_precomp f (𝟙 D) Z h
  simp only [CategoryTheory.Functor.map_id, tensorHom_id] at hp
  change (PointedObject.adjoinFunctor.map f ▷ PointedObject.adjoin D) ≫ adjoinTensorMap Z h =
    adjoinTensorMap Z ((f ▷ D) ≫ h) at hp
  rw [hp]
  exact adjoinTensorMap_zero Z _ hf

/-- 概要：通常の右境界を基点へ送る条件は点つきの右境界の零化を与える。
方針：基点追加の自然性と定数射の零化を使う。
規約：全高次単体の等号を入力とする。使われ方：右 cofiber の降下条件。 -/
lemma adjoinTensorMap_right_zero {B C D : SSet.{u}} (g : C ⟶ D)
    (Z : PointedSimplicialSet.{u}) (h : B ⊗ D ⟶ Z.right)
    (hg : (B ◁ g) ≫ h = CartesianMonoidalCategory.toUnit (B ⊗ C) ≫ Z.hom) :
    (PointedObject.adjoin B ◁ PointedObject.adjoinFunctor.map g) ≫ adjoinTensorMap Z h = 0 := by
  have hp := adjoinTensorMap_precomp (𝟙 B) g Z h
  simp only [CategoryTheory.Functor.map_id, id_tensorHom] at hp
  change (PointedObject.adjoin B ◁ PointedObject.adjoinFunctor.map g) ≫ adjoinTensorMap Z h =
    adjoinTensorMap Z ((B ◁ g) ≫ h) at hp
  rw [hp]
  exact adjoinTensorMap_zero Z _ hg

/-- 概要：通常の積の両境界を基点へ送る射を cofiber の smash からの射に降ろす。
方針：自由な基点を加えた射に二つの cofiber の降下を適用する。
規約：通常の点つき単体集合の構成。使われ方：反復 S の suspension 構造射。 -/
def rawCofiberTensorDesc {A B C D : SSet.{u}} (f : A ⟶ B) (g : C ⟶ D)
    (Z : PointedSimplicialSet.{u}) (h : B ⊗ D ⟶ Z.right)
    (hf : (f ▷ D) ≫ h = CartesianMonoidalCategory.toUnit (A ⊗ D) ≫ Z.hom)
    (hg : (B ◁ g) ≫ h = CartesianMonoidalCategory.toUnit (B ⊗ C) ≫ Z.hom) :
    PointedObject.cofiber f ⊗ PointedObject.cofiber g ⟶ Z :=
  cofiberTensorDesc f g Z (adjoinTensorMap Z h)
    (adjoinTensorMap_left_zero f Z h hf) (adjoinTensorMap_right_zero g Z h hg)

/-- 概要：二つの商写像で引き戻すと自由な基点を加えた元の射を回収する。
方針：二段の cofiber の降下の式。
規約：smash 上の厳密等号。使われ方：構造射の cylinder との照合。 -/
lemma rawCofiberTensorDesc_quotient {A B C D : SSet.{u}} (f : A ⟶ B) (g : C ⟶ D)
    (Z : PointedSimplicialSet.{u}) (h : B ⊗ D ⟶ Z.right) (hf) (hg) :
    (PointedObject.cofiberProjection f ⊗ₘ PointedObject.cofiberProjection g) ≫
      rawCofiberTensorDesc f g Z h hf hg = adjoinTensorMap Z h :=
  cofiberTensorDesc_quotient f g Z _ _ _

end SerrePositivity.KST.SConstruction
