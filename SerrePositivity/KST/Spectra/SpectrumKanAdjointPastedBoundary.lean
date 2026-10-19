module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointSpecifiedPasting

/-!
概要：上下の指定三角形を保持して貼った元の正方形の左右の境界を、同じ実区間で計算する。
方針：輸送・相対帰納正方形の端点の式を正規化した辺へ戻す。
規約：元の構造区間が始点境界に残る。使われ方：全列区間の両端固定性への残条件の検査。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A B : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence) (j : B ⟶ A) [Mono j.right]

/-- 合成正方形の始点境界は、元の Kan 随伴の同じ構造区間そのもの。 -/
lemma kanAdjointRelativeTracedPastedSquare_start (n : ℕ) :
    SquareAdjustment.leftSide ≫ (kanAdjointRelativeTracedPastedSquare X Y φ j n).h =
      (kanAdjointTracedStructureInterval X Y φ n).path := by
  rw [kanAdjointRelativeTracedPastedSquare_left, kanAdjointCanonicalAdjustedTransport_left]
  have h := kanAdjointCanonicalTransportSquare_start X Y φ j n
  rw [SquareAdjustment.face_left, Category.assoc] at h
  have he := congrArg (CartesianMonoidalCategory.lift
    (stdSimplex.isTerminalObj₀.from (Δ[1] : SSet.{u})) (𝟙 _) ≫ ·) h
  simp only [← Category.assoc, lift_snd, Category.id_comp] at he
  change SquareAdjustment.leftSide ≫ (kanAdjointCanonicalTransportHomotopy X Y φ j n).h =
    (kanAdjointTracedStructureInterval X Y φ n).path at he
  exact he

/-- 合成正方形の終点境界は、厳密化した同じ列の構造射の頂点で全体が一定。 -/
lemma kanAdjointRelativeTracedPastedSquare_finish (n : ℕ) :
    SquareAdjustment.rightSide ≫ (kanAdjointRelativeTracedPastedSquare X Y φ j n).h =
      SSet.const (PointedMapping.familyVertex
        (PointedSimplicialSet.circle.{u} ◁ (kanAdjointRelativeTracedParameterHom X Y φ j).app n ≫
          (KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).sigma n)) := by
  rw [kanAdjointRelativeTracedPastedSquare_right]
  have h := compositionTriangleSquare_finish (kanAdjointRelativeTracedTriangle X Y φ j n)
  rw [SquareAdjustment.face_right, Category.assoc, edgeId_yonedaEquiv_symm] at h
  have he := congrArg (CartesianMonoidalCategory.lift
    (stdSimplex.isTerminalObj₀.from (Δ[1] : SSet.{u})) (𝟙 _) ≫ ·) h
  simp only [← Category.assoc, lift_snd, Category.id_comp, SSet.comp_const] at he
  change SquareAdjustment.rightSide ≫
      (kanAdjointRelativeTracedStructureHomotopy X Y φ j n).h =
    SSet.const (PointedMapping.familyVertex
      (PointedSimplicialSet.circle.{u} ◁ (kanAdjointRelativeTracedParameterHom X Y φ j).app n ≫
        (KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).sigma n)) at he
  exact he

end SerrePositivity.KST.Spectra.RawSpectrumMapping
