module
public import SerrePositivity.KST.SConstruction.TerminalFiberContraction
public import SerrePositivity.KST.SConstruction.ZeroRowPathContraction

/-! # 元の零行収縮の終点固定 fiber 内でのホモトピー
概要：元の零行収縮をそのまま使い、境界の loop と定数 path の fiber 比較を結ぶ。
方針：一時刻の厳密な零境界を suffix の fiber ホモトピーへ渡す。
規約：元の Kan 全空間と元の収縮の向きを保つ。使われ方：実際の構造射の随伴の Ω 条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

/-- 元の零行収縮の一時刻の境界は厳密に基点。 -/
lemma zeroRowPathContraction_terminalBoundary (r : ℕ) (X : StableModel.{u}) :
    SSet.ι₁ ≫ zeroRowPathContraction r X ≫
      (pointedFullIteratedPathKanBoundary r X).right =
        toUnit ((iteratedPathRealizationDiagram r X).obj (Opposite.op ⦋0⦌)) ≫
          ((boundaryKanRealizationFunctor r).obj X).hom := by
  rw [← Category.assoc, zeroRowPathContraction_one, zeroRowPathToKan_boundary]

/-- 元の零行から終点固定 fiber への定数 path による比較。 -/
def zeroRowTerminalFiberComparison (r : ℕ) (X : StableModel.{u}) :
    (iteratedPathRealizationDiagram r X).obj (Opposite.op ⦋0⦌) ⟶
      (terminalPathHomotopyFiber (pointedFullIteratedPathKanBoundary r X)).right :=
  terminalStrictZeroFiberMap (pointedFullIteratedPathKanBoundary r X)
    (zeroRowPathToKan r X) (zeroRowPathToKan_boundary r X)

/-- 元の零行収縮の境界 loop と全空間の基点の組を終点固定 fiber に取る。 -/
def zeroRowTerminalLoopFiberComparison (r : ℕ) (X : StableModel.{u}) :
    (iteratedPathRealizationDiagram r X).obj (Opposite.op ⦋0⦌) ⟶
      (terminalPathHomotopyFiber (pointedFullIteratedPathKanBoundary r X)).right :=
  terminalPathFamilyFiberMap (pointedFullIteratedPathKanBoundary r X)
    (zeroRowPathContraction r X) (zeroRowPathContraction_terminalBoundary r X)

/-- 元の零行収縮から得る fiber 比較の実際のホモトピー。 -/
def zeroRowTerminalFiberHomotopy (r : ℕ) (X : StableModel.{u}) :
    SSet.Homotopy (zeroRowTerminalLoopFiberComparison r X)
      (zeroRowTerminalFiberComparison r X) := by
  simpa only [zeroRowTerminalLoopFiberComparison, zeroRowTerminalFiberComparison,
    zeroRowPathContraction_one] using
    terminalFiberHomotopy (pointedFullIteratedPathKanBoundary r X)
      (zeroRowPathContraction r X) (zeroRowPathContraction_terminalBoundary r X)

/-- ホモトピーの零時刻の射は元の全空間の基点上にある。 -/
lemma zeroRowTerminalLoopFiberComparison_projection (r : ℕ) (X : StableModel.{u}) :
    zeroRowTerminalLoopFiberComparison r X ≫
      (pullback.snd (terminalPathStart ((boundaryKanRealizationFunctor r).obj X))
        (pointedFullIteratedPathKanBoundary r X)).right =
      toUnit ((iteratedPathRealizationDiagram r X).obj (Opposite.op ⦋0⦌)) ≫
        ((pointedIteratedPathKanFunctor r).obj X).hom := by
  rw [zeroRowTerminalLoopFiberComparison, terminalPathFamilyFiberMap,
    IsPullback.lift_snd, zeroRowPathContraction_zero]

end SerrePositivity.KST.SConstruction
