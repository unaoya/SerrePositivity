module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IntervalHomTriangles
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LocalIntervalDiagramEdges
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorTriangleSquare

/-!
概要：実際の固定成分 Hom の標準正方形の、固定された三辺を全パラメーターで計算する。
方針：底の同型の自然性と頂点保持を、元の prism の三辺の式に適用する。
規約：元の図式と指定された成分を保持する。
使われ方：最初の実際の三角形を、固定二辺の可縮な延長空間へ写す。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

variable (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianTransportDiagramCategory (ULift.{u} (Fin 2)))
local notation "c" => (ULift.up (1 : Fin 2))
variable (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue F c))
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue G c))) _⦋0⦌)
local notation "E" => (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianHomIntervalEvaluation F G c) v)
local notation "D₀" => (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.qCatDiagramCoherentNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValueFunctor F))
local notation "D₁" => (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.qCatDiagramCoherentNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValueFunctor G))

/-- 実際の標準正方形の始点の辺は、元の始域図式の同じ標準区間上の表示。 -/
lemma cocartesianIntervalHomSquare_zero {T : SSet.{u + 1}} (f : T ⟶ E) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[1] ▷ T) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIntervalHomSquare F G v f =
      fst (Δ[1] : SSet.{u + 1}) T ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.localKanDiagramBaseIso 1).hom ≫ D₀ := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIntervalHomSquare
  rw [← Category.assoc, ← comp_whiskerRight, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality,
    comp_whiskerRight, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianHomFixedComponentPrism_zero,
    ← Category.assoc, whiskerRight_fst, Category.assoc]

/-- 実際の標準正方形の終点の辺は、元の標的図式の同じ標準区間上の表示。 -/
lemma cocartesianIntervalHomSquare_one {T : SSet.{u + 1}} (f : T ⟶ E) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[1] ▷ T) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIntervalHomSquare F G v f =
      fst (Δ[1] : SSet.{u + 1}) T ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.localKanDiagramBaseIso 1).hom ≫ D₁ := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIntervalHomSquare
  rw [← Category.assoc, ← comp_whiskerRight, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality,
    comp_whiskerRight, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianHomFixedComponentPrism_one,
    ← Category.assoc, whiskerRight_fst, Category.assoc]

/-- 実際の標準正方形の右側の辺は、指定された元の成分の区間族に定値。 -/
lemma cocartesianIntervalHomSquare_at_one {T : SSet.{u + 1}} (f : T ⟶ E) :
    (lift (𝟙 (Δ[1] : SSet.{u + 1}))
      (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ▷ T) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIntervalHomSquare F G v f =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (SSet.const v : T ⟶ _) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIntervalHomSquare
  rw [← Category.assoc, ← comp_whiskerRight, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.localIntervalDiagramBaseIso_side]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianHomFixedComponentPrism_at F G c v f

/-- 最初の実際の三角形の前辺は、元の始域図式の辺に全パラメーターで定値。 -/
lemma cocartesianIntervalHomTriangle_first {T : SSet.{u + 1}} (f : T ⟶ E) :
    (stdSimplex.δ (2 : Fin 3) ▷ T) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIntervalHomTriangle F G v 0 f =
      fst (Δ[1] : SSet.{u + 1}) T ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.localKanDiagramBaseIso 1).hom ≫ D₀ := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIntervalHomTriangle
  rw [← Category.assoc, ← comp_whiskerRight, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleSquare_upper_left]
  exact cocartesianIntervalHomSquare_zero F G v f

/-- 最初の実際の三角形の後辺は、指定された元の成分に全パラメーターで定値。 -/
lemma cocartesianIntervalHomTriangle_last {T : SSet.{u + 1}} (f : T ⟶ E) :
    (stdSimplex.δ (0 : Fin 3) ▷ T) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIntervalHomTriangle F G v 0 f =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (SSet.const v : T ⟶ _) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIntervalHomTriangle
  rw [← Category.assoc, ← comp_whiskerRight, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleSquare_upper_top]
  exact cocartesianIntervalHomSquare_at_one F G v f

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
