module

public import SerrePositivity.Spectra.PointedSimplicialSet.SmashUnderlying
public import Mathlib.CategoryTheory.Monoidal.Functor
public import SerrePositivity.CategoryTheory.Enriched.BaseChange

/-! # 基点を忘れたsmashの標準射と結合・交換の両立 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.PointedSimplicialSet

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits

/-- 基点付き直積の結合子の基礎射は単体的集合の直積の結合子。 -/
lemma productAssociator_underlying (X Y Z : PointedSimplicialSet.{u}) :
    (PointedObject.prodAssocHom X Y Z).right = (α_ X.right Y.right Z.right).hom := by
  rfl

/-- 三つの直積からsmashへ送る標準射は結合子と両立する。 -/
lemma productToSmash_associator (X Y Z : PointedSimplicialSet.{u}) :
    productToSmash X Y ▷ Z.right ≫ productToSmash (X ⊗ Y) Z ≫
      (α_ X Y Z).hom.right =
    (α_ X.right Y.right Z.right).hom ≫ X.right ◁ productToSmash Y Z ≫
      productToSmash X (Y ⊗ Z) := by
  have h := congrArg (fun k => k.right) (PointedObject.leftTripleQuotient_assocHom X Y Z)
  change (productToSmash X Y ⊗ₘ 𝟙 Z.right) ≫ productToSmash (X ⊗ Y) Z ≫
    (α_ X Y Z).hom.right = (PointedObject.prodAssocHom X Y Z).right ≫
      (𝟙 X.right ⊗ₘ productToSmash Y Z) ≫ productToSmash X (Y ⊗ Z) at h
  rw [tensorHom_id, id_tensorHom, productAssociator_underlying] at h
  exact h

/-- 基点付き直積の交換の基礎射は単体的集合の直積の交換。 -/
lemma productSwap_underlying (X Y : PointedSimplicialSet.{u}) :
    (PointedObject.prodSwap X Y).right = (β_ X.right Y.right).hom := by
  rfl

/-- 二つの直積からsmashへ送る標準射は交換と両立する。 -/
lemma productToSmash_braiding (X Y : PointedSimplicialSet.{u}) :
    (β_ X.right Y.right).hom ≫ productToSmash Y X =
      productToSmash X Y ≫ (β_ X Y).hom.right := by
  have h := congrArg (fun k => k.right) (PointedObject.smashQuotient_swap X Y)
  change productToSmash X Y ≫ (β_ X Y).hom.right =
    (PointedObject.prodSwap X Y).right ≫ productToSmash Y X at h
  rw [productSwap_underlying] at h
  exact h.symm

/-- 基点を忘れる関手の単位比較は零次球面の非基点側を選ぶ。 -/
def forgetUnit : 𝟙_ SSet.{u} ⟶ (𝟙_ PointedSimplicialSet.{u}).right :=
  unitUnderlyingHom (𝟙_ PointedSimplicialSet.{u}) (𝟙 _)

/-- 忘却の単位比較は自由な基点の追加の第一包含。 -/
lemma forgetUnit_eq : forgetUnit.{u} = CategoryTheory.Limits.coprod.inl := by
  change (CategoryTheory.Limits.coprod.inl : 𝟙_ SSet.{u} ⟶
    (𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u})) ≫ 𝟙 _ = _
  rw [Category.comp_id]

/-- 忘却の単位比較からの合成は非基点側を選んだ通常の射。 -/
lemma forgetUnit_comp (X : PointedSimplicialSet.{u})
    (f : 𝟙_ PointedSimplicialSet.{u} ⟶ X) :
    forgetUnit ≫ f.right = unitUnderlyingHom X f := by
  rw [forgetUnit_eq]
  rfl

/-- 直積からsmashへの標準射は左単位と両立する。 -/
lemma productToSmash_left_unitor (X : PointedSimplicialSet.{u}) :
    forgetUnit ▷ X.right ≫ productToSmash (𝟙_ PointedSimplicialSet.{u}) X ≫
      (λ_ X).hom.right = (λ_ X.right).hom := by
  have h := congrArg (fun k => k.right) (PointedObject.smashQuotient_leftUnitHom X)
  change productToSmash (𝟙_ PointedSimplicialSet.{u}) X ≫ (λ_ X).hom.right =
    PointedObject.leftUnitRaw X at h
  rw [forgetUnit_eq, h]
  exact PointedObject.leftUnitRaw_first X

/-- 直積からsmashへの標準射は右単位とも両立する。 -/
lemma productToSmash_right_unitor (X : PointedSimplicialSet.{u}) :
    X.right ◁ forgetUnit ≫ productToSmash X (𝟙_ PointedSimplicialSet.{u}) ≫
      (ρ_ X).hom.right = (ρ_ X.right).hom := by
  change X.right ◁ forgetUnit ≫ productToSmash X (𝟙_ PointedSimplicialSet.{u}) ≫
    (β_ X (𝟙_ PointedSimplicialSet.{u})).hom.right ≫ (λ_ X).hom.right = _
  rw [← reassoc_of% (productToSmash_braiding X (𝟙_ PointedSimplicialSet.{u}))]
  have hn := BraidedCategory.braiding_naturality (𝟙 X.right) forgetUnit.{u}
  rw [id_tensorHom, tensorHom_id] at hn
  rw [reassoc_of% hn, productToSmash_left_unitor]
  exact braiding_leftUnitor X.right

/-- 基点を忘れる関手の直積からsmashへの比較によるlax monoidal構造。 -/
instance forget_laxMonoidal : forget.{u}.LaxMonoidal where
  ε := forgetUnit
  μ := productToSmash
  μ_natural_left f X := by
    have h := productToSmash_naturality f (𝟙 X)
    simp only [Under.id_right, tensorHom_id] at h
    exact h
  μ_natural_right X f := by
    have h := productToSmash_naturality (𝟙 X) f
    simp only [Under.id_right, id_tensorHom] at h
    exact h
  associativity := productToSmash_associator
  left_unitality X := (productToSmash_left_unitor X).symm
  right_unitality X := (productToSmash_right_unitor X).symm

/-- 忘却の比較はsmashの交換と通常の直積の交換を両立させる。 -/
instance forget_laxBraided : forget.{u}.LaxBraided where
  toLaxMonoidal := forget_laxMonoidal
  braided X Y := (productToSmash_braiding X Y).symm

/-- 零次球面からの射と基礎単体的集合の単位からの射の同値。 -/
def forgetUnitHomEquiv (X : PointedSimplicialSet.{u}) :
    (𝟙_ PointedSimplicialSet.{u} ⟶ X) ≃ (𝟙_ SSet.{u} ⟶ forget.obj X) :=
  PointedObject.adjoinHomEquiv (𝟙_ SSet.{u}) X

/-- 単位からの射の同値は忘却関手の単位比較による射に一致する。 -/
lemma forgetUnitHomEquiv_formula (X : PointedSimplicialSet.{u})
    (f : 𝟙_ PointedSimplicialSet.{u} ⟶ X) :
    forgetUnitHomEquiv X f = LaxPointHom.map forget f := (forgetUnit_comp X f).symm

end SerrePositivity.PointedSimplicialSet
