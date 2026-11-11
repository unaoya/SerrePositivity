module
public import SerrePositivity.KST.SConstruction.PointedSuspensionEvaluation

/-! # 元の円を固定する suspension 全族の直積上の回収
概要：全パラメータ族の suspension を、元の円と対象の直積上の同じ作用で表す。
方針：全単体の評価公式を自然変換の等号へ束ねる。
規約：元の商射と全高次入力を保持する。使われ方：Ex∞ suspension 比較の全族自然性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet

/-- 全 suspension 族の作用は、元の円を固定した実作用として商射上で厳密に回収される。 -/
lemma suspensionFamily_evaluation {P : SSet.{u}} (X Y : PointedSimplicialSet.{u})
    (a : P ⟶ (PointedObject.basedHom X Y).right) :
    (PointedSimplicialSet.productToSmash PointedSimplicialSet.circle.{u} X ▷ P) ≫
      uncurry (a ≫ (Spectra.suspensionHom X Y).right ≫
        PointedObject.basedHomι (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension Y)) =
    (α_ PointedSimplicialSet.circle.{u}.right X.right P).hom ≫
      (PointedSimplicialSet.circle.{u}.right ◁ uncurry (a ≫ PointedObject.basedHomι X Y)) ≫
      PointedSimplicialSet.productToSmash PointedSimplicialSet.circle.{u} Y := by
  ext n t
  exact suspensionHom_family_app X Y a n t.1.1 t.1.2 t.2

/-- 全 suspension 族の作用後の点つき射も、元の商射と実作用の指定式で回収される。 -/
lemma suspensionFamily_evaluation_post {P : SSet.{u}} (X Y Z : PointedSimplicialSet.{u})
    (a : P ⟶ (PointedObject.basedHom X Y).right) (g : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension Y ⟶ Z)
    (b : X.right ⊗ P ⟶ Y.right)
    (c : PointedSimplicialSet.circle.{u}.right ⊗ Y.right ⟶ Z.right)
    (hb : uncurry (a ≫ PointedObject.basedHomι X Y) = b)
    (hc : PointedSimplicialSet.productToSmash PointedSimplicialSet.circle.{u} Y ≫ g.right = c) :
    (PointedSimplicialSet.productToSmash PointedSimplicialSet.circle.{u} X ▷ P) ≫
      (uncurry (a ≫ (Spectra.suspensionHom X Y).right ≫
        PointedObject.basedHomι (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension Y)) ≫ g.right) =
    (α_ PointedSimplicialSet.circle.{u}.right X.right P).hom ≫
      (PointedSimplicialSet.circle.{u}.right ◁ b) ≫ c := by
  erw [← Category.assoc, suspensionFamily_evaluation]
  conv_lhs => erw [Category.assoc, Category.assoc]
  erw [hc, hb]


end SerrePositivity.KST.SConstruction
