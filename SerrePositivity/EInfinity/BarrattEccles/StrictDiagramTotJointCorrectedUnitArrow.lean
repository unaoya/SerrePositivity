module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.ArrowMiddleUnit
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrowVertexEdgeNerve
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointCorrectionComponentArrows
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceUnitLabel

/-!
概要：元の単位ラベルの corrected pairing の辺の類は、元の native 恒等射と一致する。
方針：同じ成分の三辺の合成則へ元の左右射影の実射を代入して相殺する。
規約：元の全補正比較と同じ単位ラベルを使い、端点は Arrow の等式で保持する。
使われ方：元の全 native 比較の同じ単位の評価への接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomotopicalAlgebra SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.HA.StableInfinityCategories
noncomputable section

namespace SerrePositivity.EInfinity.BarrattEccles

variable (A : Type u) [CommRing A]
local instance jointCorrectedUnitArrowModel : ModelCategory (operad A).Algebra := modelCategory A
local instance jointCorrectedUnitArrowFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩

/-- 元の同じ補正単位の辺の類は、元の native 試験対象の恒等射の Arrow に一致する。 -/
lemma strictBETotJointSourceCorrectedPairing_unit_arrow (X : (operad A).Algebra) :
    Arrow.mk (HomotopyCategory.homMk (twistedArrowVertexEdge
      ((strictBETotJointSourceCorrectedPairing A).app (Opposite.op ⦋0⦌)
        (nerveVertex (strictBETotJointSourceUnitLabel A X))))) =
      Arrow.mk (𝟙 (HomotopyCategory.mk ((strictBETotModelSource A).app
        (Opposite.op ⦋0⦌) (nerveVertex (modelRelativeObject (operad A).Algebra X))))) := by
  let t := strictBETotJointSourceUnitLabel A X
  let a := (strictBETotJointSourceCorrectedPairing A).app (Opposite.op ⦋0⦌) (nerveVertex t)
  let b := (strictBETotJointSourceNativePairing A).app (Opposite.op ⦋0⦌) (nerveVertex t)
  let f := ((strictBETotJointSourceCorrectedPairingIso A).app (nerveVertex t)).hom
  let p := ((homotopyOppositeEquivalence (CAlg_R A)).functor.map
    ((SSet.mapHomotopyCategory (edgewiseLeft (CAlg_R A))).map f)).unop
  let r := (SSet.mapHomotopyCategory (edgewiseRight (CAlg_R A))).map f
  let aHom := HomotopyCategory.homMk (twistedArrowVertexEdge a)
  let bHom := HomotopyCategory.homMk (twistedArrowVertexEdge b)
  let gAug := (AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).map
    ((strictBETotJointRoofResolution A t.obj.1).augmentation.app t.obj.2.unop ≫
      framedLimitProbeComparison A (AsSmall.down.obj t.obj.1).1.unop)
  let gUnit := (AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).map
    ((rightFrameReplacementUnit (rightFrameFamily A)).app (AsSmall.down.obj t.obj.1).2)
  let p₀ := HomotopyCategory.homMk ((nerve.edgeMk gAug).map (strictBETotModelSource A))
  let r₀ := HomotopyCategory.homMk ((nerve.edgeMk gUnit).map (strictBETotModelSource A))
  let : IsIso f := by dsimp only [f]; infer_instance
  let : IsIso p := by dsimp only [p]; infer_instance
  let : IsIso r := by dsimp only [r]; infer_instance
  have hp : Arrow.mk p = Arrow.mk p₀ := strictBETotJointSourceCorrection_left_component_arrow A t
  have hr : Arrow.mk r = Arrow.mk r₀ := strictBETotJointSourceCorrection_right_component_arrow A t
  have hpt := congrArg (fun v : (TwistedArrow (CAlg_R A)) _⦋0⦌ =>
    Arrow.mk (HomotopyCategory.homMk (twistedArrowVertexEdge v)))
      (strictBETotJointSourceUnitLabel_native_pairing A X)
  have hb₀ := hpt.trans (twistedArrowVertexEdge_nerve_arrow (strictBETotModelSource A) _)
  have hb₁ : Arrow.mk bHom =
      Arrow.mk (HomotopyCategory.homMk ((nerve.edgeMk (gAug ≫ gUnit)).map
        (strictBETotModelSource A))) := by
    rw [CategoryTheory.Functor.map_comp] at hb₀
    exact hb₀
  have hb : Arrow.mk bHom = Arrow.mk (p₀ ≫ r₀) :=
    hb₁.trans (congrArg Arrow.mk (mappedNerveEdgeHom_comp (strictBETotModelSource A) gAug gUnit))
  have hc : p ≫ aHom ≫ r = bHom := strictBETotJointSourceCorrection_component_composition A t
  exact arrow_middle_unit_of_outer_arrow_equalities p aHom r bHom p₀ r₀ hp hr hb hc

end SerrePositivity.EInfinity.BarrattEccles

end
