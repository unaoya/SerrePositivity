module

public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.PointedPrismFixedSource

/-!
概要：動く始点の lift 空間を固定始点へ制限した終点評価の同値性。
方針：prism を保つ同型で既存の全 lift の終点同値性へ移す。
規約：始点写像を固定した底変換全体についての結論。
使われ方：Kerodon Lemma 5.6.9.1 の中間空間の fiber ごとの比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：固定始点の比較同型は終点評価を厳密に保つ。
方針：fiber の包含後で普遍 prism の終点を比較する。
規約：関手同型でなく射そのものの等式。
使われ方：終点評価の同値性の新旧の空間間の移送。 -/
lemma pointedPrismFixedSourceIso_endpoint {K : SSet.{u + 1}} {s : SpaceInfinity.{u} _⦋0⦌}
    (f : K ⟶ vertexFiber pointedSpaceProjection s) (t : SpaceInfinity.{u} _⦋0⦌) :
    (pointedPrismFixedSourceIso f t).hom ≫
      ((fiberTransportFamily pointedSpaceProjection f
        (intervalMappingUncurry (𝟙 (intervalMappingSpace s t)))
        (intervalMappingUncurry_zero _) (intervalMappingUncurry_one _)).liftSpaceTransportFamily
          (intervalMappingUncurry_one _)).map =
    pullback.fst (pointedPrismLiftParameters K s t) (pointedPrismFixedSourceParameter f t) ≫
      pointedPrismLiftEndpoint K s t := by
  dsimp only [FiberTransportFamily.map, FiberTransportFamily.liftSpaceTransportFamily,
    pointedPrismLiftEndpoint, prismLiftSpaceEndpoint]
  apply uncurry_injective
  change uncurry (_ ≫ curry _) = uncurry (_ ≫ curry _)
  rw [uncurry_natural_left, uncurry_curry, uncurry_natural_left, uncurry_curry]
  apply vertexFiber_hom_ext pointedSpaceProjection t
  simp only [Category.assoc, vertexFiberLift_ι]
  calc
    _ = prismEndpoint 1 _ ≫ (Δ[1] ◁ (K ◁ (pointedPrismFixedSourceIso f t).hom)) ≫
        (fiberTransportFamily pointedSpaceProjection f
          (intervalMappingUncurry (𝟙 (intervalMappingSpace s t)))
          (intervalMappingUncurry_zero _) (intervalMappingUncurry_one _)).liftSpacePrism := by
      simpa only [Category.assoc] using congrArg (fun w ↦ w ≫
        (fiberTransportFamily pointedSpaceProjection f
          (intervalMappingUncurry (𝟙 (intervalMappingSpace s t)))
          (intervalMappingUncurry_zero _) (intervalMappingUncurry_one _)).liftSpacePrism)
        (prismEndpoint_naturality 1 (K ◁ (pointedPrismFixedSourceIso f t).hom)).symm
    _ = _ := (congrArg (fun w ↦ prismEndpoint 1 _ ≫ w)
      (pointedPrismFixedSourceIso_prism f t)).trans (by
        rw [← Category.assoc, prismEndpoint_naturality, Category.assoc]
        rfl)

/-- 概要：始点を固定する底変換の空間は quasicategory。
方針：パラメーター射影の trivial Kan fibration を底変換する。
規約：始点 f は任意で係数 K の充填性は不要。
使われ方：固定始点の終点評価の同値性を適用する。 -/
instance pointedPrismFixedSource_quasicategory {K : SSet.{u + 1}}
    {s : SpaceInfinity.{u} _⦋0⦌} (f : K ⟶ vertexFiber pointedSpaceProjection s)
    (t : SpaceInfinity.{u} _⦋0⦌) :
    Quasicategory (pullback (pointedPrismLiftParameters K s t)
      (pointedPrismFixedSourceParameter f t)) := by
  let : TrivialKanFibration (pullback.snd (pointedPrismLiftParameters K s t)
      (pointedPrismFixedSourceParameter f t)) := trivialKanFibration_pullback_snd _ _
  exact quasicategory_of_innerFibration (pullback.snd _ _)

/-- 概要：始点を同値に固定した全 lift 空間の終点評価は同値。
方針：固定始点の比較同型と既証明の普遍輸送の終点同値性を合成する。
規約：動く始点の空間の底変換上の実際の終点射についての結論。
使われ方：同時の始点・終点制限の fiber ごとの同値性。 -/
lemma pointedPrismFixedSourceEndpoint_isQCatEquivalence {K : SSet.{u + 1}}
    [Quasicategory K] {s : SpaceInfinity.{u} _⦋0⦌}
    (f : K ⟶ vertexFiber pointedSpaceProjection s) (hf : IsQCatEquivalence f)
    (t : SpaceInfinity.{u} _⦋0⦌) :
    IsQCatEquivalence (pullback.fst (pointedPrismLiftParameters K s t)
      (pointedPrismFixedSourceParameter f t) ≫ pointedPrismLiftEndpoint K s t) := by
  rw [← pointedPrismFixedSourceIso_endpoint]
  exact (isPrecompositionEquivalence_of_iso (pointedPrismFixedSourceIso f t)).isQCatEquivalence.comp
    (pointedUniversalPrismLiftEndpoint_isQCatEquivalence s t f hf)

end SerrePositivity.InfinityCategories
