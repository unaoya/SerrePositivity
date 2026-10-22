module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowTerminalCoconeFamily
public import SerrePositivity.InfinityCategories.F2.Ind.ArrowInterpolationTipLine

/-!
概要：終端辺固定の普遍全余錐を元の円柱形状へ戻し、同じ全区間 D を回収する。
方針：全円柱同型の逆と終端辺の厳密な計算を使う。
規約：全パラメーターで元の指定区間図式を保持。使われ方：元の図式 comma への帰還。
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

/-- 全終端辺を固定した比較の普遍族を、元の全円柱へ戻す。 -/
def indArrowTerminalPrismFamily :
    (join T (Δ[0] : SSet.{u + 1}) ⊗ Δ[1]) ⊗ indArrowTerminalLiftFamily W ⟶ IndInfinity κ C :=
  ((arrowInterpolationCoconeIso T).inv ▷ indArrowTerminalLiftFamily W) ≫
    indArrowTerminalCoconeFamily W

/-- 元の余錐頂点上では、帰還した普遍族は同じ元の全区間 D に厳密に定値。 -/
lemma indArrowTerminalPrismFamily_tip :
    ((joinInr T (Δ[0] : SSet.{u + 1}) ▷ Δ[1]) ▷ indArrowTerminalLiftFamily W) ≫
      indArrowTerminalPrismFamily W =
        (snd (Δ[0] : SSet.{u + 1}) Δ[1] ▷ indArrowTerminalLiftFamily W) ≫
          fst Δ[1] (indArrowTerminalLiftFamily W) ≫ (liftedIntervalToSmall.{u} ≫ D) := by
  have hi := congrArg (fun f => (f ▷ indArrowTerminalLiftFamily W) ≫
    indArrowTerminalCoconeFamily W) (arrowInterpolationCoconeIso_inv_tip T)
  calc
    _ = (snd (Δ[0] : SSet.{u + 1}) Δ[1] ▷ indArrowTerminalLiftFamily W) ≫
        ((joinStdSimplexIso 0 0).inv ▷ indArrowTerminalLiftFamily W) ≫
          (joinMap (arrowInterpolationSourceTip T) (𝟙 Δ[0]) ▷ indArrowTerminalLiftFamily W) ≫
            indArrowTerminalCoconeFamily W := by
      simpa only [indArrowTerminalPrismFamily, arrowInterpolationTipLine,
        comp_whiskerRight, Category.assoc] using hi
    _ = _ := by
      rw [indArrowTerminalCoconeFamily_terminalEdge]
      simp only [whiskerRight_fst_assoc, Iso.inv_hom_id_assoc]

end SerrePositivity.InfinityCategories.F2.Ind
