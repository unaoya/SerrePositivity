module

public import SerrePositivity.InfinityCategories.F2.Ind.FixedArrowPrismBoundary

/-!
概要：終端辺固定の比較 fiber を、元の全円柱の両指定境界の fiber へ写す。
方針：普遍族の二つの全境界を curry し、同じ元の実 fiber へ持ち上げる。
規約：C 側の全図式と D 全体を全次数で固定。使われ方：元の q の全変換の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {κ : Cardinal.{u}} {C : SSet.{u}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C}
  {T : SSet.{u + 1}} {q : T ⟶ diagramComma κ D}
  {H : T ⟶ pullback (indYoneda κ C) (sliceOverProjection D)}
  (W : IndArrowSlicePrism κ D q H)
local notation "a" => indArrowOriginalFamily κ D q ≫ indYoneda κ C
local notation "d" => liftedIntervalToSmall ≫ D

/-- 元の試験族側への全制限は、curry の後も同じ全図式に定値。 -/
lemma indArrowTerminalPrismCurry_old : curry (indArrowTerminalPrismFamily W) ≫
    (pre (joinInl T (Δ[0] : SSet.{u + 1}) ▷ Δ[1])).app (IndInfinity κ C) =
      SSet.const (functorVertex a) := by
  apply uncurry_injective
  rw [uncurry_pre_app, uncurry_curry, indArrowTerminalPrismFamily_old,
    uncurry_const_functorVertex]

/-- 指定頂点側への全制限も、curry の後に同じ全区間図式に定値。 -/
lemma indArrowTerminalPrismCurry_tip : curry (indArrowTerminalPrismFamily W) ≫
    (pre (joinInr T (Δ[0] : SSet.{u + 1}) ▷ Δ[1])).app (IndInfinity κ C) =
      SSet.const (functorVertex (snd (Δ[0] : SSet.{u + 1}) Δ[1] ≫ d)) := by
  apply uncurry_injective
  rw [uncurry_pre_app, uncurry_curry, indArrowTerminalPrismFamily_tip,
    whiskerRight_fst_assoc, uncurry_const_functorVertex]

/-- 比較の全族を、元の二つの指定全境界を固定した円柱 fiber へ写す。 -/
def indArrowTerminalPrismBoundaryMap :
    indArrowTerminalLiftFamily W ⟶ fixedArrowPrismBoundary a d :=
  vertexFiberLift _ _ (curry (indArrowTerminalPrismFamily W)) (by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, arrowPrismBoundaryRestriction, lift_fst, SSet.const_comp]
      exact indArrowTerminalPrismCurry_old W
    · rw [Category.assoc, arrowPrismBoundaryRestriction, lift_snd, SSet.const_comp]
      exact indArrowTerminalPrismCurry_tip W)

end SerrePositivity.InfinityCategories.F2.Ind
