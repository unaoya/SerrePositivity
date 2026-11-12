module
public import SerrePositivity.KST.Fibration.VerdierOriginalFullSCompositeVertices
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionTriangle
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ControlledTriangleReadoutMap

/-!
概要：元の全 S• 比較の動く実合成端を、上側再構成の第二短辺全族にする。
方針：第一短辺を元の core 包含に固定し、同じ全円柱の合成端を標準宇宙へ上げる。
規約：第二短辺を定値へ置き換えず、元の比較の非退化一単体を保持する。
使われ方：K-6 c4 の指定有限端点と共有対角を同時に持つ実上側全族。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants

namespace SerrePositivity.KST.Fibration
variable (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u})

/-- 概要：同じ実 core 包含を第一短辺の全族として固定する。
方針：元の core から全 S• への実 Kan 射の豊穣頂点を定値にする。
規約：元の対象と実射を保持する。
使われ方：動く上側再構成の第一短辺。 -/
def verdierMovingUpperFirstFamily :
    (Δ[1] : SSet.{u + 1}) ⟶ (SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom
        (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left))
        (fullSRealizationKanObject d.left)) :=
  SSet.const (ULift.up (SimplicialCategory.homEquiv' _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (coreSFullRealizationInclusion (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left)))))

/-- 概要：同じ実全 S• 比較の動く合成端を第二短辺の全族として使う。
方針：元の実区間写像を同じ標準単体同型で宇宙持ち上げする。
規約：全比較円柱の同じ合成端を保持する。
使われ方：元の二つの実完全射を両端に持つ上側第二短辺。 -/
def verdierMovingUpperLastFamily :
    (Δ[1] : SSet.{u + 1}) ⟶ (SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom (fullSRealizationKanObject d.left)
        (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right))) :=
  (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, u + 1} 1).inv ≫
    (SSet.uliftFunctor.{u + 1, u}).map (verdierOriginalFullSCompositePath d 0 1)

/-- 概要：元の固定包含と動く実第二短辺の全族の豊穣合成。
方針：F1 正本の同じ全族合成へ元の二つの実短辺を代入する。
規約：元の動く第二短辺を保持する。
使われ方：上側長 Hom 入力の合成端条件。 -/
def verdierMovingUpperCompositeFamily :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCompositeFamily
    (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left))
    (fullSRealizationKanObject d.left)
    (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right)) Δ[1]
    (verdierMovingUpperFirstFamily d) (verdierMovingUpperLastFamily d)

/-- 概要：同じ固定包含と動く実第二短辺を全パラメータで持つ実内ホーン。
方針：元の二短辺の標準 coherent 合成三角形から同じ二面を読む。
規約：新しい存在仮定や非指定のホーン充填は使わない。
使われ方：Ind-S (9) の実 canonical encoder への固定ホーン入力。 -/
def verdierMovingUpperHorn :
    (Λ[2, 1] : SSet.{u + 1}) ⊗ Δ[1] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  ((horn 2 (1 : Fin 3)).ι ▷ (Δ[1] : SSet.{u + 1})) ≫
    (Δ[2] ◁ lift (verdierMovingUpperFirstFamily d) (verdierMovingUpperLastFamily d)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionTriangle
        (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left))
        (fullSRealizationKanObject d.left)
        (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right))

/-- 概要：同じ実ホーンの第一短辺は元の固定 core 包含の標準区間像。
方針：F1 正本の合成三角形の第一面を全パラメータで制限する。
規約：実全族の厳密等式。
使われ方：再構成の第一短辺条件。 -/
theorem verdierMovingUpperHorn_first :
    (horn₂₁.ι₀₁ ▷ (Δ[1] : SSet.{u + 1})) ≫ verdierMovingUpperHorn d =
      (Δ[1] ◁ verdierMovingUpperFirstFamily d) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison
          (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left))
          (fullSRealizationKanObject d.left)) := by
  rw [verdierMovingUpperHorn, ← Category.assoc, ← comp_whiskerRight, horn.ι_ι]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionTriangle_first_precomp]
  simp only [lift_fst_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]

/-- 概要：同じ実ホーンの第二短辺は元の動く全 S• 比較の標準区間像。
方針：同じ合成三角形の第二面を元の動く族で制限する。
規約：全パラメータの非退化一単体を保持する。
使われ方：再構成の第二短辺条件。 -/
theorem verdierMovingUpperHorn_last :
    (horn₂₁.ι₁₂ ▷ (Δ[1] : SSet.{u + 1})) ≫ verdierMovingUpperHorn d =
      (Δ[1] ◁ verdierMovingUpperLastFamily d) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison
          (fullSRealizationKanObject d.left)
          (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right))) := by
  rw [verdierMovingUpperHorn, ← Category.assoc, ← comp_whiskerRight, horn.ι_ι]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionTriangle_last_precomp]
  simp only [lift_snd_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]

end SerrePositivity.KST.Fibration
