module

public import SerrePositivity.InfinityCategories.F2.Ind.DiagramPrismGluingBoundary
public import SerrePositivity.InfinityCategories.F2.Ind.DiagramRightPrismRecovery
public import SerrePositivity.InfinityCategories.F2.Ind.DiagramCommaOriginalFamilyNaturality

/-!
概要：形状 pushout 上の元の diagram comma の全族を、元の両制限を厳密に保って貼る。
方針：C 全族と D への全円柱を貼り、同じ実 comma の族へ戻す。
規約：共通境界を全射で明示し、同型への置き換えを行わない。
使われ方：極大点の追加で、元の旧族と指定下方余錐を貼り合わせる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
  {J K₁ K₂ K : SSet.{u}} {i : J ⟶ K₁} {j : J ⟶ K₂}
  {r : K₁ ⟶ K} {s : K₂ ⟶ K} (h : IsPushout i j r s)
  (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ IndInfinity κ C) {T : SSet.{u + 1}}
  (q₁ : T ⟶ diagramComma κ ((SSet.uliftFunctor.{u + 1, u}).map r ≫ D))
  (q₂ : T ⟶ diagramComma κ ((SSet.uliftFunctor.{u + 1, u}).map s ≫ D))
  (hP : (T ◁ (SSet.uliftFunctor.{u + 1, u}).map i) ≫
      diagramCommaOriginalFamily κ _ q₁ =
    (T ◁ (SSet.uliftFunctor.{u + 1, u}).map j) ≫ diagramCommaOriginalFamily κ _ q₂)
  (hW : (join T (Δ[0] : SSet.{u + 1}) ◁ (SSet.uliftFunctor.{u + 1, u}).map i) ≫
      diagramCommaRightPrism κ _ q₁ =
    (join T (Δ[0] : SSet.{u + 1}) ◁ (SSet.uliftFunctor.{u + 1, u}).map j) ≫
      diagramCommaRightPrism κ _ q₂)
/-- 概要：元の両局所族を同じ元の図式 comma の全族として貼る。
方針：元の全族と全円柱の pushout。規約：全境界。使われ方：点追加の実貼り合わせ。 -/
def diagramCommaGlue : T ⟶ diagramComma κ D :=
  diagramRightPrismFamily κ D
    (tensorShapeGlue h (diagramCommaOriginalFamily κ _ q₁) (diagramCommaOriginalFamily κ _ q₂) hP)
    (tensorShapeGlue h (diagramCommaRightPrism κ _ q₁) (diagramCommaRightPrism κ _ q₂) hW)
    (tensorShapeGlue_prism_old h (indYoneda κ C) _ _ _ _ hP hW
      (diagramCommaRightPrism_old κ _ q₁) (diagramCommaRightPrism_old κ _ q₂))
    (tensorShapeGlue_prism_tip h _ _ hW D
      (diagramCommaRightPrism_tip κ _ q₁) (diagramCommaRightPrism_tip κ _ q₂))
/-- 概要：貼った全族の左制限は元の指定左族自身。
方針：元の C 全族と全円柱で照合。規約：全射の等号。使われ方：旧族の厳密な回収。 -/
lemma diagramCommaGlue_left : diagramCommaGlue κ h D q₁ q₂ hP hW ≫
    diagramCommaRestriction κ D r = q₁ := by
  apply diagramComma_rightFamily_ext κ ((SSet.uliftFunctor.{u + 1, u}).map r ≫ D)
  · rw [← diagramCommaOriginalFamily_restrict, diagramCommaGlue,
      diagramRightPrismFamily_originalFamily, tensorShapeGlue_left]
  · rw [← diagramCommaRightPrism_restrict, diagramCommaGlue,
      diagramRightPrismFamily_prism, tensorShapeGlue_left]
/-- 概要：貼った全族の右制限は元の指定右族自身。
方針：元の C 全族と全円柱で照合。規約：全射の等号。使われ方：指定余錐の厳密な回収。 -/
lemma diagramCommaGlue_right : diagramCommaGlue κ h D q₁ q₂ hP hW ≫
    diagramCommaRestriction κ D s = q₂ := by
  apply diagramComma_rightFamily_ext κ ((SSet.uliftFunctor.{u + 1, u}).map s ≫ D)
  · rw [← diagramCommaOriginalFamily_restrict, diagramCommaGlue,
      diagramRightPrismFamily_originalFamily, tensorShapeGlue_right]
  · rw [← diagramCommaRightPrism_restrict, diagramCommaGlue,
      diagramRightPrismFamily_prism, tensorShapeGlue_right]
end SerrePositivity.InfinityCategories.F2.Ind
