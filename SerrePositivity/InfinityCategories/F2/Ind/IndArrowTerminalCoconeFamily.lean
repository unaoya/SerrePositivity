module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowTerminalSliceFamily
public import SerrePositivity.InfinityCategories.F2.Ind.RelativeSliceCoconeFixedSource

/-!
概要：全終端辺を固定する持ち上げの普遍 uncurry は、元の全区間 D を全次数で固定する。
方針：sourceTip での相対族の定値性を、その右余錐全体へ移す。
規約：元の同じ全区間図式を保持。使われ方：元の図式 comma への同型の帰還。
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
local notation "p" => stdSimplex.δ 0 ≫ (liftedIntervalToSmall ≫ D)
local notation "b" => indArrowSlicePrismBaseCone (q := q)
local notation "j" => joinInl (arrowInterpolationCorner T) Δ[0]
local notation "f" => indArrowSlicePrismCone W

/-- sourceTip 上の元の slice 図式の全辺は、元の同じ区間図式そのもの。 -/
lemma indArrowTerminalSliceSource_uncurry :
    sliceOverUncurry (arrowInterpolationSourceTip T ≫ (j ≫ f)) =
      (joinStdSimplexIso 0 0).hom ≫ (liftedIntervalToSmall.{u} ≫ D) := by
  have h := congrArg (fun r => joinInl (Δ[0] : SSet.{u + 1}) Δ[0] ≫ r)
    (indArrowSlicePrismCone_terminalEdge W)
  simp only [← Category.assoc, joinInl_joinMap, joinStdSimplexIso_zero_inl] at h
  have hs : arrowInterpolationSourceTip T ≫ (j ≫ f) =
      stdSimplex.δ 1 ≫ intervalTerminalSliceSection (liftedIntervalToSmall.{u} ≫ D) := by
    simpa only [Category.assoc] using h
  rw [hs, intervalTerminalSliceSection_first]

/-- 全終端辺を固定した実持ち上げ fiber 上の、元の全余錐の普遍族。 -/
def indArrowTerminalCoconeFamily :
    join (arrowInterpolationCorner T) Δ[0] ⊗ indArrowTerminalLiftFamily W ⟶ IndInfinity κ C :=
  (join (arrowInterpolationCorner T) Δ[0] ◁ indArrowTerminalSliceFamily W) ≫
    relativeSliceCoconeUncurry p (j ≫ b)

/-- 普遍全余錐の終端辺は、全パラメーターで元の同じ全区間 D に厳密に固定される。 -/
lemma indArrowTerminalCoconeFamily_terminalEdge :
    (joinMap (arrowInterpolationSourceTip T) (𝟙 Δ[0]) ▷ indArrowTerminalLiftFamily W) ≫
      indArrowTerminalCoconeFamily W =
        fst (join (Δ[0] : SSet.{u + 1}) Δ[0]) (indArrowTerminalLiftFamily W) ≫
          (joinStdSimplexIso 0 0).hom ≫ (liftedIntervalToSmall.{u} ≫ D) := by
  have hp : (arrowInterpolationSourceTip T ≫ (j ≫ f)) ≫ sliceOverProjection p =
      arrowInterpolationSourceTip T ≫ (j ≫ b) := by
    have h := congrArg (fun r => arrowInterpolationSourceTip T ≫ j ≫ r)
      (indArrowSlicePrismCone_projection W)
    simpa only [Category.assoc] using h
  have h := relativeSliceCoconeUncurry_fixedSource p (j ≫ b) (arrowInterpolationSourceTip T)
    (indArrowTerminalSliceFamily W) (arrowInterpolationSourceTip T ≫ (j ≫ f)) hp
    (indArrowTerminalSliceFamily_sourceTip W)
  simpa only [indArrowTerminalCoconeFamily, Category.assoc,
    indArrowTerminalSliceSource_uncurry] using h

end SerrePositivity.InfinityCategories.F2.Ind
