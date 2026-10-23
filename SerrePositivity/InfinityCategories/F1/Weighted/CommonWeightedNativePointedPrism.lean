module

public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.PointedCosliceDisplay
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.PointedPrismBaseChange
public import SerrePositivity.InfinityCategories.F1.Weighted.KanLeftCutConeOne
public import SerrePositivity.InfinityCategories.F1.Categories.KanDiagramNativeOppositeHomParameter
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.StrictKanCommonWeightedComparison

/-!
概要：完成した左切断 coslice prism を、元の共通 weighted 始域の pointed prism へ制限する。
方針：実際の反転係数の像と元の Hom の右端からの native な係数射を使う。
規約：始点と底の全パラメーターの厳密な式を保持する。
使われ方：元の全相対 Hom への降下と実際の straightening 作用との照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

/-- 共通係数の反転側への実際の像は、元の同じ底への射影を厳密に保つ。 -/
lemma strictKanCommonOppositeWeightedImage_projection {I : Type u} [SmallCategory I]
    (F : I ⥤ KanObject.{u}) :
    strictKanCommonOppositeWeightedImage F ≫ (SSet.uliftFunctor.{u + 1, u}).map
      (weightedNerveProjection
        (simplicialHomDiagram (F ⋙ kanObjectOpFunctor) pointKanObject ⋙ SSet.opFunctor)) =
    (SSet.uliftFunctor.{u + 1, u}).map (weightedNerveProjection
      (simplicialHomDiagram (strictKanCommonDiagram F) edgewisePointKanObject ⋙
        SSet.opFunctor)) := by
  have h := congrArg (fun f => f ≫
    leftUnstraighteningProjection (kanDiagramCoherentNerve (F ⋙ kanObjectOpFunctor)))
    (strictKanCommonOppositeWeightedImage_compare F)
  rw [Category.assoc, strictKanUnstraighteningComparison_projection, Category.assoc,
    strictKanCommonUnstraighteningOpposite_projection, weightedCoherentConeComparison_over] at h
  exact h

/-- 元の共通 weighted 始域と元の Hom の右端に沿う、実際の native pointed prism。 -/
def commonWeightedNativePointedPrism {I : Type u} [SmallCategory I]
    (F G : KanDiagramObject I) :
    ((Δ[1] : SSet.{u + 1}) ⊗ (SSet.uliftFunctor.{u + 1, u}).obj (weightedNerve
      (simplicialHomDiagram (strictKanCommonDiagram F.val) edgewisePointKanObject ⋙
        SSet.opFunctor))) ⊗ (SSet.uliftFunctor.{u + 1, u}).obj
          (edgewiseSubdivision (SimplicialCategory.sHom F G)) ⟶ PointedSpaceInfinity.{u} :=
  ((Δ[1] ◁ strictKanCommonOppositeWeightedImage F.val) ⊗ₘ
    ((SSet.uliftFunctor.{u + 1, u}).map (edgewiseRight (SimplicialCategory.sHom F G)) ≫
      (SSet.uliftFunctor.{u + 1, u}).map (kanDiagramNativeOppositeHomParameter F G))) ≫
    weightedKanLeftCutCoslicePrism
      (show KanDiagramObject I from ⟨F.val ⋙ kanObjectOpFunctor, trivial⟩)
      (show KanDiagramObject I from ⟨G.val ⋙ kanObjectOpFunctor, trivial⟩) pointKanObject ≫
      pointedCosliceDisplay

/-- native pointed prism の始点は、元の共通 cone 比較に続く同じ反転全空間の比較。 -/
lemma commonWeightedNativePointedPrism_zero {I : Type u} [SmallCategory I]
    (F G : KanDiagramObject I) :
    (prismEndpoint 0 _ ▷ _) ≫ commonWeightedNativePointedPrism F G =
    fst _ _ ≫ weightedCoherentConeComparison (strictKanCommonDiagram F.val)
      edgewisePointKanObject ≫ strictKanCommonUnstraighteningOpposite F.val ≫
        pullback.fst pointedSpaceProjection
          (kanDiagramCoherentNerve (F.val ⋙ kanObjectOpFunctor)) := by
  let a := strictKanCommonOppositeWeightedImage F.val
  let b := (SSet.uliftFunctor.{u + 1, u}).map
      (edgewiseRight (SimplicialCategory.sHom F G)) ≫
    (SSet.uliftFunctor.{u + 1, u}).map (kanDiagramNativeOppositeHomParameter F G)
  let F' : KanDiagramObject I := ⟨F.val ⋙ kanObjectOpFunctor, trivial⟩
  let G' : KanDiagramObject I := ⟨G.val ⋙ kanObjectOpFunctor, trivial⟩
  change (prismEndpoint 0 _ ▷ _) ≫ (((Δ[1] ◁ a) ⊗ₘ b) ≫
    weightedKanLeftCutCoslicePrism F' G' pointKanObject ≫ pointedCosliceDisplay) = _
  rw [← Category.assoc, prismEndpoint_tensorPrecomp, Category.assoc,
    ← Category.assoc (prismEndpoint 0 _ ▷ _)]
  calc
    _ = (a ⊗ₘ b) ≫ (fst _ _ ≫ weightedCosliceComparison
        (F.val ⋙ kanObjectOpFunctor) pointKanObject) ≫ pointedCosliceDisplay :=
      congrArg (fun k => (a ⊗ₘ b) ≫ k ≫ pointedCosliceDisplay)
        (weightedKanLeftCutCoslicePrism_zero F' G' pointKanObject)
    _ = _ := by
      rw [Category.assoc, ← Category.assoc (a ⊗ₘ b), tensorHom_fst, Category.assoc,
        weightedCosliceComparison_pointed, ← Category.assoc a,
        strictKanCommonOppositeWeightedImage_compare, Category.assoc]

/-- native pointed prism の終点は、元の反転 Hom 作用による合成係数と標的比較の合成。 -/
lemma commonWeightedNativePointedPrism_one {I : Type u} [SmallCategory I]
    (F G : KanDiagramObject I) :
    (prismEndpoint 1 _ ▷ _) ≫ commonWeightedNativePointedPrism F G =
    (strictKanCommonOppositeWeightedImage F.val ⊗ₘ
      ((SSet.uliftFunctor.{u + 1, u}).map (edgewiseRight (SimplicialCategory.sHom F G)) ≫
        (SSet.uliftFunctor.{u + 1, u}).map (kanDiagramNativeOppositeHomParameter F G))) ≫
      weightedKanHomCompositeFamily
        (show KanDiagramObject I from ⟨F.val ⋙ kanObjectOpFunctor, trivial⟩)
        (show KanDiagramObject I from ⟨G.val ⋙ kanObjectOpFunctor, trivial⟩) pointKanObject ≫
      strictKanUnstraighteningComparison (G.val ⋙ kanObjectOpFunctor) ≫
        pullback.fst pointedSpaceProjection
          (kanDiagramCoherentNerve (G.val ⋙ kanObjectOpFunctor)) := by
  let a := strictKanCommonOppositeWeightedImage F.val
  let b := (SSet.uliftFunctor.{u + 1, u}).map
      (edgewiseRight (SimplicialCategory.sHom F G)) ≫
    (SSet.uliftFunctor.{u + 1, u}).map (kanDiagramNativeOppositeHomParameter F G)
  let F' : KanDiagramObject I := ⟨F.val ⋙ kanObjectOpFunctor, trivial⟩
  let G' : KanDiagramObject I := ⟨G.val ⋙ kanObjectOpFunctor, trivial⟩
  change (prismEndpoint 1 _ ▷ _) ≫ (((Δ[1] ◁ a) ⊗ₘ b) ≫
    weightedKanLeftCutCoslicePrism F' G' pointKanObject ≫ pointedCosliceDisplay) = _
  rw [← Category.assoc, prismEndpoint_tensorPrecomp, Category.assoc,
    ← Category.assoc (prismEndpoint 1 _ ▷ _)]
  calc
    _ = (a ⊗ₘ b) ≫ (weightedKanHomCompositeFamily F' G' pointKanObject ≫
        weightedCosliceComparison (G.val ⋙ kanObjectOpFunctor) pointKanObject) ≫
        pointedCosliceDisplay :=
      congrArg (fun k => (a ⊗ₘ b) ≫ k ≫ pointedCosliceDisplay)
        (weightedKanLeftCutCoslicePrism_one F' G' pointKanObject)
    _ = _ := by
      rw [Category.assoc, weightedCosliceComparison_pointed]

/-- native pointed prism の底は、元の同じ反転左区間の全共同実現に厳密に一致。 -/
lemma commonWeightedNativePointedPrism_projection {I : Type u} [SmallCategory I]
    (F G : KanDiagramObject I) :
    commonWeightedNativePointedPrism F G ≫ pointedSpaceProjection =
    ((Δ[1] ◁ (SSet.uliftFunctor.{u + 1, u}).map (weightedNerveProjection
      (simplicialHomDiagram (strictKanCommonDiagram F.val) edgewisePointKanObject ⋙
        SSet.opFunctor))) ▷ _) ≫
      functorParameterizedPrism
        (intervalMappingUncurry (kanDiagramOppositeLeftHomInterval F G)) := by
  let a := strictKanCommonOppositeWeightedImage F.val
  let b := (SSet.uliftFunctor.{u + 1, u}).map
      (edgewiseRight (SimplicialCategory.sHom F G)) ≫
    (SSet.uliftFunctor.{u + 1, u}).map (kanDiagramNativeOppositeHomParameter F G)
  let F' : KanDiagramObject I := ⟨F.val ⋙ kanObjectOpFunctor, trivial⟩
  let G' : KanDiagramObject I := ⟨G.val ⋙ kanObjectOpFunctor, trivial⟩
  let H := kanEnrichedDiagramLeftHomInterval (kanDiagramUniversalEnriched I) F' G' rfl rfl
  have hn : kanDiagramOppositeLeftHomInterval F G = b ≫ H :=
    kanDiagramOppositeLeftHomInterval_eq_native F G
  change (((Δ[1] ◁ a) ⊗ₘ b) ≫ weightedKanLeftCutCoslicePrism F' G' pointKanObject ≫
    pointedCosliceDisplay) ≫ pointedSpaceProjection = _
  rw [Category.assoc, Category.assoc, pointedCosliceDisplay_projection,
    weightedKanLeftCutCoslicePrism_projection F' G' pointKanObject, ← Category.assoc]
  let q := (SSet.uliftFunctor.{u + 1, u}).map (weightedNerveProjection
    (simplicialHomDiagram (F.val ⋙ kanObjectOpFunctor) pointKanObject ⋙ SSet.opFunctor))
  calc
    _ = (((Δ[1] ◁ (a ≫ q)) ▷ _) ≫ ((Δ[1] ⊗ _) ◁ b)) ≫
        functorParameterizedPrism (intervalMappingUncurry H) :=
      congrArg (fun k => k ≫ functorParameterizedPrism (intervalMappingUncurry H))
        (prismCoefficientProjection_tensorPrecomp a q b)
    _ = _ := by
      rw [Category.assoc, hn, intervalMappingUncurry_precomp,
        functorParameterizedPrism_parameterPrecomp]
      change ((Δ[1] ◁ (strictKanCommonOppositeWeightedImage F.val ≫ _)) ▷ _) ≫ _ = _
      rw [strictKanCommonOppositeWeightedImage_projection]

end SerrePositivity.InfinityCategories
