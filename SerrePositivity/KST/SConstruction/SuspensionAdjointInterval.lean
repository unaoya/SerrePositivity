module
public import SerrePositivity.KST.SConstruction.LoopIntervalExt

/-! # 元の suspension 随伴の区間上の評価
概要：既存の suspension–loop 随伴の像を元の区間上へ戻すと、smash の商上の元の射になる。
方針：既存の smash curry の包含後の式と通常の curry の自然性を使う。
規約：元の随伴を別の同値で置換しない。使われ方：構造射の随伴と零行 loop 射の厳密な照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial

/-- 元の suspension 随伴の通常の Hom 同値は、構成済みの smash curry に一致する。 -/
lemma suspensionLoopEquiv_eq_smashCurry (Q B : PointedSimplicialSet.{u})
    (F : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension Q ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv Q B F = PointedObject.smashCurry F := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv, PointedSimplicialSet.smashHomAdjunction,
    PointedObject.smashHomAdjunction]
  rw [Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- 元の suspension 随伴の評価を、円の元の区間商と任意のパラメータ上で回収する。 -/
lemma suspensionLoopEquiv_interval {A : SSet.{u}} (Q B : PointedSimplicialSet.{u})
    (F : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension Q ⟶ B) (a : A ⟶ Q.right) :
    (PointedObject.cofiberQuotient (boundary.{u} 1).ι ▷ A) ≫
      MonoidalClosed.uncurry ((a ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv Q B F).right) ≫
        PointedObject.basedHomι PointedSimplicialSet.circle.{u} B) =
      (PointedObject.cofiberQuotient (boundary.{u} 1).ι ⊗ₘ a) ≫
        (PointedObject.smashQuotient PointedSimplicialSet.circle.{u} Q).right ≫ F.right := by
  have hc : (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv Q B F).right ≫
      PointedObject.basedHomι PointedSimplicialSet.circle.{u} B =
    MonoidalClosed.curry
      ((PointedObject.smashQuotient PointedSimplicialSet.circle.{u} Q).right ≫ F.right) :=
    by
      rw [suspensionLoopEquiv_eq_smashCurry]
      exact PointedObject.smashCurry_ι F
  rw [Category.assoc, hc, ← MonoidalClosed.curry_natural_left, MonoidalClosed.uncurry_curry]
  rw [tensorHom_def]
  rfl

end SerrePositivity.KST.SConstruction
