module

public import SerrePositivity.KST.Spectra.PointedTracedPathBoundary
public import SerrePositivity.KST.Spectra.FreePathEvaluation
public import SerrePositivity.KST.Spectra.PointedBasedPathCalculus
public import SerrePositivity.KST.Spectra.SquareBoundaryFamilies
public import SerrePositivity.KST.Spectra.PointedVerticalPathFiber

/-!
概要：写像 path に保持した同じ移送トレースを、両端境界固定の実正方形に読む。
方針：自由 path の通常の評価へ、保存済みの四辺の等式を適用する。
規約：新たな区間や充填を選ばない。使われ方：普遍交換の自然性正方形との貼り合わせ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.PointedMapping.TracedPathLift

variable {T E B : PointedSimplicialSet.{u}} {q : E ⟶ B} {f g : T ⟶ E}
  {P : VerticalPath (PointedObject.toPoint B) (f ≫ q) (g ≫ q)} (L : TracedPathLift q P)

/-- 移送した区間の元の像と、指定した downstairs 区間を結ぶ同じ実正方形。 -/
def traceSquare : SSet.Homotopy ((L.path.basedPost q).path) P.path where
  h := FreePathEvaluation.square L.tracePath
  h₀ := (FreePathEvaluation.square_zero L.tracePath).trans L.tracePath_start
  h₁ := (FreePathEvaluation.square_one L.tracePath).trans L.tracePath_finish
  rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim

/-- トレース正方形の左辺全体は、元の始点の同じ厳密な頂点で一定。 -/
lemma traceSquare_start :
    SquareAdjustment.leftSide ≫ L.traceSquare.h = SSet.const (familyVertex (f ≫ q)) := by
  have hs : SquareAdjustment.leftSide.{u} =
      lift (stdSimplex.isTerminalObj₀.from (Δ[1] : SSet.{u})) (𝟙 _) ≫
        stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u}) := by
    apply CartesianMonoidalCategory.hom_ext <;> rfl
  change SquareAdjustment.leftSide ≫ FreePathEvaluation.square L.tracePath = _
  rw [hs, Category.assoc, FreePathEvaluation.square_pre, L.tracePath_zero,
    FreePathEvaluation.square_constant, ← Category.assoc, lift_fst,
    pointFamily_eq_const, SSet.comp_const]

/-- 右辺全体も、元の終点の同じ厳密な頂点で一定。 -/
lemma traceSquare_finish :
    SquareAdjustment.rightSide ≫ L.traceSquare.h = SSet.const (familyVertex (g ≫ q)) := by
  have hs : SquareAdjustment.rightSide.{u} =
      lift (stdSimplex.isTerminalObj₀.from (Δ[1] : SSet.{u})) (𝟙 _) ≫
        stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u}) := by
    apply CartesianMonoidalCategory.hom_ext <;> rfl
  change SquareAdjustment.rightSide ≫ FreePathEvaluation.square L.tracePath = _
  rw [hs, Category.assoc, FreePathEvaluation.square_pre, L.tracePath_one,
    FreePathEvaluation.square_constant, ← Category.assoc, lift_fst,
    pointFamily_eq_const, SSet.comp_const]

end SerrePositivity.KST.Spectra.PointedMapping.TracedPathLift
