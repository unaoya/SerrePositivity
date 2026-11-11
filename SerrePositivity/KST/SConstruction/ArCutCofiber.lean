module
public import SerrePositivity.KST.SConstruction.ArCutShapes

/-! # 切断四角形の cofiber 性
概要：gapped 図式の任意の切断四角形が零角と押し出し性を持つことを示す。
方針：左右の退化四角形と切断点を跨ぐ gapped 四角形に場合分けする。
規約：零角は元の (k,k) に厳密に一致する。使われ方：切断による相対 cofiber 図式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 切断四角形の零角は元の切断位置の対角をそのまま保持する。 -/
lemma arCutSquareAt_zero_corner {n : ℕ} {C : SSet.{u}} (k : Fin (n + 1))
    (a : Ar.{u} n) (F : arNerve n ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (arCutSquareAt k a ≫ F) 0 1 =
      F.app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ (arObj k k le_rfl)) := by
  apply congrArg (F.app (Opposite.op ⦋0⦌))
  apply ComposableArrows.ext₀
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext <;> exact cutEndpoint_zero_one k _

/-- 任意の切断位置の四角形は gapped 性から実際に押し出しとなる。 -/
lemma arCutSquareAt_isPushout {n : ℕ} {C : SSet.{u}} [Quasicategory C]
    (k : Fin (n + 1)) (a : Ar.{u} n) {F : arNerve n ⟶ C} (hF : IsGapped F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (arCutSquareAt k a ≫ F) := by
  by_cases hl : a.down.val.2 ≤ k
  · rw [arCutSquareAt_left k a hl, Category.assoc]
    exact identityPushoutShape_isPushout false _
  by_cases hr : k ≤ a.down.val.1
  · rw [arCutSquareAt_right k a hr, Category.assoc]
    exact identityPushoutShape_isPushout true _
  have hi : a.down.val.1 ≤ k := (le_total _ _).resolve_right hr
  have hj : k ≤ a.down.val.2 := (le_total _ _).resolve_left hl
  rw [arCutSquareAt_crossing k a hi hj]
  exact hF.2 _ _ _ _ _ _ _

/-- 任意の切断位置の四角形は元の零対角を持つ cofiber 四角形。 -/
lemma arCutSquareAt_isCofiber {n : ℕ} {C : SSet.{u}} [Quasicategory C]
    (k : Fin (n + 1)) (a : Ar.{u} n) {F : arNerve n ⟶ C} (hF : IsGapped F) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (arCutSquareAt k a ≫ F) 0 1) ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (arCutSquareAt k a ≫ F) := by
  refine ⟨?_, arCutSquareAt_isPushout k a hF⟩
  rw [arCutSquareAt_zero_corner]
  exact hF.1 k

end SerrePositivity.KST.SConstruction
