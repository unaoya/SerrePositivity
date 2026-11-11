module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberRightAdjointTarget

public import SerrePositivity.KST.LocalizingInvariants.CofiberAdjunction

/-!
概要：cofiber の実右随伴の矢印の終域は、元の入力対象そのものである。
方針：四角形の共通角、右辺切断の厳密性、恒等矢印の始点評価を使う。
規約：全単体上の厳密な等式。使われ方：右随伴を零始点矢印として同定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- 元の入力対象は右随伴の矢印の終域に全単体上で厳密に残る。 -/
lemma cofiberRightAdjoint_target (X : SSet.{u}) [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    cofiberRightAdjoint X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      𝟙 X := by
  simp only [cofiberRightAdjoint, CofiberRotation.inverseRotation, Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.cofiber_bottom_target_eq_right_source]
  rw [← Category.assoc (CofiberRotation.rightSection X), CofiberRotation.rightSection_right,
    Category.id_comp]
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.identityArrow_source X

end SerrePositivity.KST.LocalizingInvariants
