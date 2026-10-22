module
public import SerrePositivity.KST.SConstruction.PointedSSetObject
public import SerrePositivity.Spectra.Pointed.AdjoinBasepoint

/-! # 全単体的な族の自由点つき表示と自然性
概要：単体集合をパラメータとする族を、自由基点追加からの同じ点つき射に移す。
方針：元の余積の Hom 同値と基点保存を使う。
規約：パラメータの Kan 性は要求しない。使われ方：実押し出しの basedHom 族の降下。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Limits SSet

/-- 全単体的な族を、同じ自由点つきパラメータからの射にする。 -/
def pointedFreeFamily {P : SSet.{u}} {X : PointedSimplicialSet.{u}} (a : P ⟶ X.right) :
    PointedObject.adjoin P ⟶ X :=
  (PointedObject.adjoinHomEquiv P X).symm a

/-- 自由点つき表示を元の族へ戻すと、同じ全パラメータの族を回収する。 -/
lemma pointedFreeFamily_recover {P : SSet.{u}} {X : PointedSimplicialSet.{u}}
    (a : P ⟶ X.right) :
    PointedObject.adjoinHomEquiv P X (pointedFreeFamily a) = a :=
  (PointedObject.adjoinHomEquiv P X).apply_symm_apply a

/-- 元の自由点つき射も、同じ族に戻してから厳密に回収される。 -/
lemma pointedFreeFamily_inverse {P : SSet.{u}} {X : PointedSimplicialSet.{u}}
    (a : PointedObject.adjoin P ⟶ X) :
    pointedFreeFamily (PointedObject.adjoinHomEquiv P X a) = a :=
  (PointedObject.adjoinHomEquiv P X).symm_apply_apply a

/-- 自由点つき表示は、全パラメータの族の等号を反映する。 -/
lemma pointedFreeFamily_injective {P : SSet.{u}} {X : PointedSimplicialSet.{u}} :
    Function.Injective (pointedFreeFamily (P := P) (X := X)) :=
  (PointedObject.adjoinHomEquiv P X).symm.injective

/-- 同じ点つき射での後合成は、自由点つき表示に厳密に自然。 -/
lemma pointedFreeFamily_post {P : SSet.{u}} {X Y : PointedSimplicialSet.{u}}
    (a : P ⟶ X.right) (f : X ⟶ Y) :
    pointedFreeFamily (a ≫ f.right) = pointedFreeFamily a ≫ f := by
  apply Under.UnderMorphism.ext
  change coprod.desc (a ≫ f.right) Y.hom = coprod.desc a X.hom ≫ f.right
  apply coprod.hom_ext
  · simp only [coprod.inl_desc, coprod.inl_desc_assoc]
  · simpa only [coprod.inr_desc, coprod.inr_desc_assoc] using (Under.w f).symm

end SerrePositivity.KST.SConstruction
