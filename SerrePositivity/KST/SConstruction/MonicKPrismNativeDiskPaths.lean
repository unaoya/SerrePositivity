module
public import SerrePositivity.KST.SConstruction.FamilyTriangleFaces
public import SerrePositivity.KST.SConstruction.MonicKPrismNativePastingTraces
public import SerrePositivity.KST.SConstruction.FamilyChainTraceSplitting

/-! # 元の K 比較複体の両側の実全辺路
概要：元の全三角形と全交換列から、両側の実補正辺路を内部構成する。
方針：元の三面を端点の合う円柱にし、同じ全交換列の二境界を通る。
規約：全区間と順序を保持し、貼り合わせ複体内の元の trace へ厳密に照合する。
使われ方：元の次段補正から共有末尾を切り出し、全 raw 比較を構成する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet Spectra
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 元の合成面と全交換列の一境界を通る実辺路。 -/
def monicKPrismNativeDiskDirectPath (n : ℕ) :=
  familyTriangleStripDirect
    (familyTriangleDirect (monicKPrismCompositionNativeTriangle n F f g))
    (monicKPrismNativeSecondCompatibilityTransport F f g n) (.nil _)

/-- 元の第一面・全交換列の零境界・出口を通る実辺路。 -/
def monicKPrismNativeDiskProjectedPath (n : ℕ) :=
  familyTriangleStripProjected
    (familyTriangleFirst (monicKPrismCompositionNativeTriangle n F f g))
    (monicKPrismNativeSecondCompatibilityTransport F f g n) (.nil _)

/-- 複体内の全セルの実像は、元の同じ二次元補正列の全 trace。 -/
lemma monicKPrismNativePastingMap_cells_transport_trace (n : ℕ) :
    (monicKPrismNativePastingCells F f g n).map (· ≫ monicKPrismNativePastingMap F f g n) =
      familyHomotopyChainTrace (monicKPrismNativeSecondCompatibilityTransport F f g n) :=
  triangleCylinderPastingMap_cells _ _

/-- 一側の実辺路の全区間は、同じ実複体の合成面と全一境界。 -/
lemma monicKPrismNativeDiskDirectPath_trace (n : ℕ) :
    familyHomotopyChainTrace (monicKPrismNativeDiskDirectPath F f g n) =
      ((nerve (CompositionStringParameters f g) ◁ stdSimplex.δ 1) ≫
        monicKPrismNativePastingTriangle F f g n ≫ monicKPrismNativePastingMap F f g n) ::
      (monicKPrismNativePastingCells F f g n).map (fun q =>
        (SSet.ι₁ (X := nerve (CompositionStringParameters f g)) ▷ (Δ[1] : SSet.{u})) ≫
          q ≫ monicKPrismNativePastingMap F f g n) := by
  rw [monicKPrismNativeDiskDirectPath, familyTriangleStripDirect_trace]
  simp only [familyHomotopyChainTrace, List.append_nil]
  rw [← monicKPrismNativePastingMap_cells_transport_trace]
  simp only [List.map_map, Function.comp_def]
  rw [monicKPrismNativePastingMap_triangle]
  rfl

/-- 他側の実辺路は、同じ実複体の第一面・全零境界・出口の全区間。 -/
lemma monicKPrismNativeDiskProjectedPath_trace (n : ℕ) :
    familyHomotopyChainTrace (monicKPrismNativeDiskProjectedPath F f g n) =
      ((nerve (CompositionStringParameters f g) ◁ stdSimplex.δ 2) ≫
        monicKPrismNativePastingTriangle F f g n ≫ monicKPrismNativePastingMap F f g n) ::
      ((monicKPrismNativePastingCells F f g n).map (fun q =>
        (SSet.ι₀ (X := nerve (CompositionStringParameters f g)) ▷ (Δ[1] : SSet.{u})) ≫
          q ≫ monicKPrismNativePastingMap F f g n) ++
        [monicKPrismNativePastingTarget F f g n ≫ monicKPrismNativePastingMap F f g n]) := by
  rw [monicKPrismNativeDiskProjectedPath, familyTriangleStripProjected_trace]
  rw [← monicKPrismNativePastingMap_cells_transport_trace]
  simp only [familyHomotopyChainTrace, List.map_map, Function.comp_def]
  rw [monicKPrismNativePastingMap_triangle, monicKPrismNativePastingMap_target]
  rfl

/-- 次段の元の全補正列を構造射へ制限した実全列。 -/
def monicKPrismNativeProjectedCorrectionChain (n : ℕ) :=
  familyHomotopyChainMap (monicKPrismNativeCompositeCorrectionChain F f g (n + 1))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((kOmegaSpectrum (F.obj x)).sigma n)
      ((kKanSequence (F.obj z)).level (n + 1)).space)

/-- 元の全射影 trace は、構成した辺路と同じ元の共通末尾の連結そのもの。 -/
lemma monicKPrismNativeProjectedCorrectionChain_trace (n : ℕ) :
    familyHomotopyChainTrace (monicKPrismNativeProjectedCorrectionChain F f g n) =
      familyHomotopyChainTrace (monicKPrismNativeDiskProjectedPath F f g n) ++
        (monicKPrismCompositeSecondTrace F f g n).map (fun h =>
          (compositionStringPair f g ▷ (Δ[1] : SSet.{u})) ≫ h ≫
            RawSpectrumMapping.step (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n) := by
  rw [monicKPrismNativeProjectedCorrectionChain, familyHomotopyChainMap_trace]
  refine (monicKPrismNativePasting_projected_full_trace F f g n).trans ?_
  rw [monicKPrismNativeDiskProjectedPath_trace]
  simp only [List.cons_append, List.append_assoc]
  rfl

/-- 構成した元の射影側辺路には、元の第一面という実区間がある。 -/
lemma monicKPrismNativeDiskProjectedPath_trace_ne_nil (n : ℕ) :
    familyHomotopyChainTrace (monicKPrismNativeDiskProjectedPath F f g n) ≠ [] := by
  rw [monicKPrismNativeDiskProjectedPath_trace]
  exact List.cons_ne_nil _ _

end SerrePositivity.KST.SConstruction
