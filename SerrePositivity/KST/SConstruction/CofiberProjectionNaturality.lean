module
public import SerrePositivity.KST.SConstruction.RawCofiberTensorDesc
public import SerrePositivity.KST.SConstruction.CofiberTensorExt

/-! # 自由な基点の射影と積上の射の自然性
概要：cofiber の底の商射影の可換式を点つき射影へ移し、基点を加えた積上の射の後合成を計算する。
方針：自由な基点の Hom 同値で非基点成分だけを比較する。
規約：通常の点つき射の厳密等号。使われ方：suspension の構造射の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet

/-- 概要：cofiber の商射影の可換式は自由な基点を加えた射影の可換式を与える。
方針：基点追加の Hom 同値で元の対象上の成分を比較する。
規約：境界間の射は追加仮定しない。使われ方：suspension 射影の自然性。 -/
lemma cofiberProjection_naturality_of_quotient {A B C D : SSet.{u}}
    (f : A ⟶ B) (g : C ⟶ D) (a : B ⟶ D)
    (k : PointedObject.cofiber f ⟶ PointedObject.cofiber g)
    (hk : PointedObject.cofiberQuotient f ≫ k.right = a ≫ PointedObject.cofiberQuotient g) :
    PointedObject.adjoinFunctor.map a ≫ PointedObject.cofiberProjection g =
      PointedObject.cofiberProjection f ≫ k := by
  apply (PointedObject.adjoinHomEquiv B (PointedObject.cofiber g)).injective
  change coprod.inl ≫ (PointedObject.adjoinFunctor.map a ≫ PointedObject.cofiberProjection g).right =
    coprod.inl ≫ (PointedObject.cofiberProjection f ≫ k).right
  simp only [Under.comp_right, PointedObject.adjoinFunctor, Under.homMk_right,
    coprod.inl_map_assoc]
  rw [PointedObject.cofiberProjection_underlying, ← Category.assoc,
    PointedObject.cofiberProjection_underlying]
  exact hk.symm

/-- 概要：基点を加えた積上の射は点つき後合成と両立する。
方針：基点追加の Hom 同値で非基点成分を比較する。
規約：底の射の後合成を使う。使われ方：構造射の自然性の標的側。 -/
lemma adjoinTensorMap_postcomp {A B : SSet.{u}} {Z W : PointedSimplicialSet.{u}}
    (h : A ⊗ B ⟶ Z.right) (k : Z ⟶ W) :
    adjoinTensorMap Z h ≫ k = adjoinTensorMap W (h ≫ k.right) := by
  unfold adjoinTensorMap
  rw [Category.assoc]
  congr 1
  apply (PointedObject.adjoinHomEquiv (A ⊗ B) W).injective
  simp [PointedObject.adjoinHomEquiv, Under.comp_right]

end SerrePositivity.KST.SConstruction
