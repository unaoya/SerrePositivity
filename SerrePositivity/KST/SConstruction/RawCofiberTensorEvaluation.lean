module
public import SerrePositivity.KST.SConstruction.RawCofiberTensorDesc
public import SerrePositivity.Spectra.PointedSimplicialSet.SmashUnderlying

/-! # 二つの元の商射による smash 降下の評価
概要：両 cofiber の元の商射から、smash 上の降下を元の直積上で回収する。
方針：自由基点の非基点成分と、smash 商の二変数自然性を比較する。
規約：点つき射と基礎射を明示する。使われ方：元の suspension 組み立ての全族自然性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet

/-- 自由基点の元の二成分上では、smash へ移した射は元の積上の射と一致する。 -/
lemma adjoinTensorMap_underlying {A B : SSet.{u}} (Z : PointedSimplicialSet.{u})
    (h : A ⊗ B ⟶ Z.right) :
    (coprod.inl ⊗ₘ coprod.inl) ≫
      PointedSimplicialSet.productToSmash (PointedObject.adjoin A) (PointedObject.adjoin B) ≫
        (adjoinTensorMap Z h).right = h := by
  have hs := congrArg Under.Hom.right (PointedObject.smashQuotient_adjoinSmashHom A B)
  change (PointedObject.smashQuotient (PointedObject.adjoin A)
    (PointedObject.adjoin B)).right ≫ (PointedObject.adjoinSmashHom A B).right =
      PointedObject.adjoinProductRaw A B at hs
  change (coprod.inl ⊗ₘ coprod.inl) ≫
    (PointedObject.smashQuotient (PointedObject.adjoin A) (PointedObject.adjoin B)).right ≫
      ((PointedObject.adjoinSmashHom A B).right ≫
        ((PointedObject.adjoinHomEquiv (A ⊗ B) Z).symm h).right) = h
  erw [reassoc_of% hs, ← Category.assoc, PointedObject.adjoinProductRaw_first]
  exact (PointedObject.adjoinHomEquiv (A ⊗ B) Z).apply_symm_apply h

/-- 二つの元の商射と smash 商から、同じ元の両境界降下前の射を回収する。 -/
lemma rawCofiberTensorDesc_underlying {A B C D : SSet.{u}} (f : A ⟶ B) (g : C ⟶ D)
    (Z : PointedSimplicialSet.{u}) (h : B ⊗ D ⟶ Z.right)
    (hf : (f ▷ D) ≫ h = CartesianMonoidalCategory.toUnit (A ⊗ D) ≫ Z.hom)
    (hg : (B ◁ g) ≫ h = CartesianMonoidalCategory.toUnit (B ⊗ C) ≫ Z.hom) :
    (PointedObject.cofiberQuotient f ⊗ₘ PointedObject.cofiberQuotient g) ≫
      PointedSimplicialSet.productToSmash (PointedObject.cofiber f) (PointedObject.cofiber g) ≫
        (rawCofiberTensorDesc f g Z h hf hg).right = h := by
  have hq : (coprod.inl ⊗ₘ coprod.inl) ≫
      ((PointedObject.cofiberProjection f).right ⊗ₘ (PointedObject.cofiberProjection g).right) =
      PointedObject.cofiberQuotient f ⊗ₘ PointedObject.cofiberQuotient g := by
    erw [tensorHom_comp_tensorHom, PointedObject.cofiberProjection_underlying,
      PointedObject.cofiberProjection_underlying]
  have hn := PointedSimplicialSet.productToSmash_naturality
    (PointedObject.cofiberProjection f) (PointedObject.cofiberProjection g)
  have hd := congrArg Under.Hom.right (rawCofiberTensorDesc_quotient f g Z h hf hg)
  change (PointedObject.cofiberProjection f ⊗ₘ PointedObject.cofiberProjection g).right ≫
    (rawCofiberTensorDesc f g Z h hf hg).right = (adjoinTensorMap Z h).right at hd
  erw [← hq, Category.assoc, reassoc_of% hn, hd, adjoinTensorMap_underlying]

end SerrePositivity.KST.SConstruction
