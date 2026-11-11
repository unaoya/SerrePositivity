module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointTracedUnitRestriction
public import SerrePositivity.KST.Spectra.CompositionTriangleSquare
public import SerrePositivity.KST.Spectra.SquareBoundaryFamilies
public import SerrePositivity.KST.Spectra.IdentityTriangleHomotopy

/-!
概要：単位の同じ実三角形から、既存の比較と同じ非定数構造境界を持つ実正方形を構成する。
方針：元の三角形とその退化三角形を貼り、同じ内部 Hom の作用を後合成する。
規約：対角辺は元の次段評価区間の制限。第二辺の前段評価への照合は別工程。
使われ方：共通境界を持つ二つの構造正方形の実貼り合わせ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra

/-- 実三角形を展開した同じ正方形の右辺は、元の終頂点で全区間が一定。 -/
lemma compositionTriangleSquare_rightSide {E : SSet.{u}} {x y z : E _⦋0⦌}
    {a : E.Edge x y} {b : E.Edge y z} {c : E.Edge x z}
    (t : SSet.Edge.CompStruct a b c) :
    SquareAdjustment.rightSide ≫ compositionTriangleSquare t = SSet.const z := by
  have hr : SquareAdjustment.rightSide.{u} =
      CartesianMonoidalCategory.lift (stdSimplex.isTerminalObj₀.from _) (𝟙 (Δ[1] : SSet.{u})) ≫
        (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u})) := by
    apply CartesianMonoidalCategory.hom_ext <;> rfl
  rw [hr, Category.assoc, compositionTriangleSquare_finish, ← Category.assoc,
    lift_snd, Category.id_comp, edgeId_yonedaEquiv_symm]

namespace RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence)

/-- 同じ単位の実二単体を展開した、全パラメータの実構造正方形。 -/
def kanAdjointTracedUnitParameterSquare (n : ℕ) :
    SSet.Homotopy
      (((kanAdjointTracedUnitEvaluationInterval X Y φ (n + 1)).basedPost
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n)
          ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space)).path)
      ((OmegaSpectrum.tracedSignedLoopUnitStepInterval Y n).path ≫
        (kanAdjointTracedUnitStructureAction X Y φ n).right) where
  h := compositionTriangleSquare (OmegaSpectrum.tracedSignedLoopUnitTriangle Y n) ≫
    (kanAdjointTracedUnitStructureAction X Y φ n).right
  h₀ := by
    rw [← Category.assoc, compositionTriangleSquare_zero]
    have he := kanAdjointTracedUnitParameterTriangle_one_evaluation X Y φ n
    rw [kanAdjointTracedUnitParameterTriangle, ← Category.assoc,
      SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm] at he
    exact he
  h₁ := by
    rw [← Category.assoc, compositionTriangleSquare_one]
    have he := kanAdjointTracedUnitParameterTriangle_zero X Y φ n
    rw [kanAdjointTracedUnitParameterTriangle, ← Category.assoc,
      SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm] at he
    exact he
  rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim

/-- 正方形の始点境界は、既存の比較に残っていた同じ元の構造区間そのもの。 -/
lemma kanAdjointTracedUnitParameterSquare_start (n : ℕ) :
    SquareAdjustment.leftSide ≫ (kanAdjointTracedUnitParameterSquare X Y φ n).h =
      (kanAdjointParameterStructureInterval X Y φ n).path := by
  have hf := kanAdjointTracedUnitParameterTriangle_two X Y φ n
  rw [kanAdjointTracedUnitParameterTriangle, ← Category.assoc,
    SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm] at hf
  have hface : stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u}) ≫
      (kanAdjointTracedUnitParameterSquare X Y φ n).h =
    snd (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫
      (kanAdjointParameterStructureInterval X Y φ n).path := by
    change _ ≫ (compositionTriangleSquare (OmegaSpectrum.tracedSignedLoopUnitTriangle Y n) ≫
      (kanAdjointTracedUnitStructureAction X Y φ n).right) = _
    rw [← Category.assoc, compositionTriangleSquare_start, Category.assoc]
    exact congrArg (snd (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ ·) hf
  have hl : SquareAdjustment.leftSide.{u} =
      CartesianMonoidalCategory.lift (stdSimplex.isTerminalObj₀.from _) (𝟙 (Δ[1] : SSet.{u})) ≫
        (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) := by
    apply CartesianMonoidalCategory.hom_ext <;> rfl
  rw [hl, Category.assoc, hface, ← Category.assoc, lift_snd, Category.id_comp]

/-- 終点境界は、同じ厳密な単位後合成の次段構造制限の頂点で全区間が一定。 -/
lemma kanAdjointTracedUnitParameterSquare_finish (n : ℕ) :
    SquareAdjustment.rightSide ≫ (kanAdjointTracedUnitParameterSquare X Y φ n).h =
      SSet.const (PointedMapping.familyVertex
        ((φ ≫ pointedPost X (OmegaSpectrum.sequenceHom (OmegaSpectrum.tracedSignedLoopUnit Y)) ≫
          pointedPost X (OmegaSpectrum.signedLoopProjection Y) ≫
          pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) (n + 1)) ≫
          _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n)
            ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space)) := by
  change SquareAdjustment.rightSide ≫
    (compositionTriangleSquare (OmegaSpectrum.tracedSignedLoopUnitTriangle Y n) ≫
      (kanAdjointTracedUnitStructureAction X Y φ n).right) = _
  rw [← Category.assoc, compositionTriangleSquare_rightSide, SSet.const_comp]
  have hd := kanAdjointTracedUnitParameterTriangle_one_evaluation X Y φ n
  rw [kanAdjointTracedUnitParameterTriangle, ← Category.assoc,
    SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm] at hd
  have hv := congrArg (fun F => SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ F)) hd
  rw [← Category.assoc, SSet.Edge.δ_zero_yonedaEquiv_symm,
    SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at hv
  rw [PointedMapping.VerticalPath.one] at hv
  exact congrArg SSet.const hv

end RawSpectrumMapping
end SerrePositivity.KST.Spectra
