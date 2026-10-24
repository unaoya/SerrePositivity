module

public import SerrePositivity.InfinityCategories.F2.Ind.IndConePrisms
public import SerrePositivity.InfinityCategories.F2.Ind.ConeSliceTwoStageLift

/-!
概要：元の試験族 q と下方余錐 G から、互換な二段の終点 slice 持ち上げを構成する。
方針：両全円柱の厳密な境界式を、一般の二段持ち上げへ渡す。
規約：元の D、両底図式、指定下方余錐と旧族の境界を保持する。
使われ方：点追加で同じ実 scalar comma の二つの全族を構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {L C : SSet.{u}} [Quasicategory C]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj (join L (Δ[0] : SSet.{u})) ⟶ IndInfinity κ C)
  {T : SSet.{u + 1}} (q : T ⟶ diagramComma κ D)
  (G : JoinCocone (q ≫ diagramCommaRestriction κ D (joinInl L (Δ[0] : SSet.{u}))))

/-- 概要：元の全底図式と全境界を保持する、互換な二段の slice 持ち上げ。
方針：元の二つの全円柱を使う。規約：全射の等号。使われ方：実 comma の両境界。 -/
structure IndConeSliceInterpolationData where
  lower : join (join T (Δ[0] : SSet.{u + 1})) Δ[0] ⊗
    (SSet.uliftFunctor.{u + 1, u}).obj L ⟶ sliceOver (indConeEndpointPoint κ D)
  prism : join T (Δ[0] : SSet.{u + 1}) ⊗
    join ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0] ⟶ sliceOver (indConeEndpointPoint κ D)
  lower_projection : lower ≫ sliceOverProjection (indConeEndpointPoint κ D) =
    indConeLowerPrism κ D q G
  lower_tip : (joinInr (join T (Δ[0] : SSet.{u + 1})) Δ[0] ▷
    (SSet.uliftFunctor.{u + 1, u}).obj L) ≫ lower =
      snd (Δ[0] : SSet.{u + 1}) ((SSet.uliftFunctor.{u + 1, u}).obj L) ≫
        joinInl ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0] ≫
          coneTerminalSliceSection (indConeNormalizedDiagram κ D)
  projection : prism ≫ sliceOverProjection (indConeEndpointPoint κ D) =
    indConeOriginalPrism κ D q
  lower_boundary : (join T (Δ[0] : SSet.{u + 1}) ◁
    joinInl ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫ prism =
      (joinMap (joinInl T (Δ[0] : SSet.{u + 1})) (𝟙 Δ[0]) ▷
        (SSet.uliftFunctor.{u + 1, u}).obj L) ≫ lower
  tip : (joinInr T (Δ[0] : SSet.{u + 1}) ▷
    join ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫ prism =
    snd (Δ[0] : SSet.{u + 1})
      (join ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫
        coneTerminalSliceSection (indConeNormalizedDiagram κ D)

/-- 概要：元の任意の q と下方の同じ余錐 G から実二段データが存在する。
方針：元の両全円柱の境界式を照合。規約：追加の充填仮定なし。使われ方：点追加。 -/
lemma indConeSliceInterpolationData_nonempty :
    Nonempty (IndConeSliceInterpolationData κ D q G) := by
  obtain ⟨U, W, hU, hUt, hW, hWl, hWt⟩ := exists_coneSlice_twoStage_lift
    (indConeNormalizedDiagram κ D) (indConeOriginalPrism κ D q) (indConeLowerPrism κ D q G)
    (indConeLowerPrism_old κ D q G) (indConeLowerPrism_tip κ D q G)
    (indConeOriginalPrism_tip κ D q)
  exact ⟨⟨U, W, hU, hUt, hW, hWl, hWt⟩⟩

end SerrePositivity.InfinityCategories.F2.Ind
