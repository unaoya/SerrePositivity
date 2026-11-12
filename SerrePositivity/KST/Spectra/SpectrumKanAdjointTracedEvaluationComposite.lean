module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointRelativeTracedComparison

/-!
概要：実構造三角形を保持した相対比較の段座標区間を、同じ境界三角形つきで名前つきに選ぶ。
方針：段調整区間と保持した相対修正区間を、指定境界の退化三角形へ持ち上げて合成する。
規約：全列の整合性は未主張。使われ方：正方形の貼り合わせの上下に指定する同じ二単体。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A B : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence) (j : B ⟶ A) [Mono j.right]

/-- 段調整と最終修正を、元の指定境界の退化三角形を保持して貼り合わせる。 -/
def kanAdjointRelativeTracedEvaluationComposite (n : ℕ) :
    { C : PointedMapping.BasedPathComposite
        (kanAdjointTracedBoundaryCoordinate X Y φ j n).interval
        (kanAdjointRelativeTracedCorrectionInterval X Y φ j n).val //
      C.path.path ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j (kanAdjointParameterTarget X Y n)).right =
          (kanAdjointTracedBoundaryInterval X Y φ j n).path ∧
      SSet.yonedaEquiv.symm C.triangle.simplex ≫
          (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j (kanAdjointParameterTarget X Y n)).right =
        SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.compId
          (kanAdjointTracedBoundaryInterval X Y φ j n).edge).simplex } := by
  let targetKan : KanComplex (kanAdjointParameterTarget X Y n).right :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
  let P := (kanAdjointTracedBoundaryCoordinate X Y φ j n).interval
  let R := kanAdjointTracedBoundaryInterval X Y φ j n
  have hP : P.path ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j (kanAdjointParameterTarget X Y n)).right =
      R.path := by
    apply PointedMapping.VerticalPath.path_restriction_eq_of_homotopy
    rw [KanAdjointBoundaryCoordinate.interval_h]
    exact kanAdjointTracedBoundaryCoordinate_comparison_boundary X Y φ j n
  let hex := PointedMapping.exists_based_composite_over_restriction j P
    (kanAdjointRelativeTracedCorrectionInterval X Y φ j n).val R hP
    (kanAdjointRelativeTracedCorrectionInterval X Y φ j n).property
  exact ⟨hex.choose, hex.choose_spec⟩

/-- 元の段座標から最終座標への同じ選択済み合成区間。 -/
def kanAdjointRelativeTracedEvaluationInterval (n : ℕ) :=
  (kanAdjointRelativeTracedEvaluationComposite X Y φ j n).val.path

/-- 選んだ実区間は、元の指定された非零境界区間そのものへ厳密に制限される。 -/
lemma kanAdjointRelativeTracedEvaluationInterval_boundary (n : ℕ) :
    j.right ▷ (Δ[1] : SSet.{u}) ≫
        (kanAdjointRelativeTracedEvaluationInterval X Y φ j n).homotopy.h =
      (kanAdjointTracedBoundaryHomotopy X Y φ j n).h :=
  PointedMapping.VerticalPath.homotopy_restriction_eq_of_path
    (kanAdjointRelativeTracedEvaluationComposite X Y φ j n).val.path
    (kanAdjointTracedBoundaryInterval X Y φ j n) j
    (kanAdjointRelativeTracedEvaluationComposite X Y φ j n).property.1

/-- 元の選択済み合成三角形を、同じ二単体族として回収する。 -/
def kanAdjointRelativeTracedEvaluationTriangle (n : ℕ) :=
  SSet.yonedaEquiv.symm (kanAdjointRelativeTracedEvaluationComposite X Y φ j n).val.triangle.simplex

/-- 第一辺は、元の段調整区間そのもの。 -/
lemma kanAdjointRelativeTracedEvaluationTriangle_two (n : ℕ) :
    stdSimplex.δ (2 : Fin 3) ≫ kanAdjointRelativeTracedEvaluationTriangle X Y φ j n =
      (kanAdjointTracedBoundaryCoordinate X Y φ j n).interval.path := by
  rw [kanAdjointRelativeTracedEvaluationTriangle, SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm]
  exact Equiv.symm_apply_apply _ _

/-- 第二辺は、保持した元の相対修正区間そのもの。 -/
lemma kanAdjointRelativeTracedEvaluationTriangle_zero (n : ℕ) :
    stdSimplex.δ (0 : Fin 3) ≫ kanAdjointRelativeTracedEvaluationTriangle X Y φ j n =
      (kanAdjointRelativeTracedCorrectionInterval X Y φ j n).val.path := by
  rw [kanAdjointRelativeTracedEvaluationTriangle, SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm]
  exact Equiv.symm_apply_apply _ _

/-- 対角辺も、同じ選択済み段座標の合成区間そのもの。 -/
lemma kanAdjointRelativeTracedEvaluationTriangle_one (n : ℕ) :
    stdSimplex.δ (1 : Fin 3) ≫ kanAdjointRelativeTracedEvaluationTriangle X Y φ j n =
      (kanAdjointRelativeTracedEvaluationInterval X Y φ j n).path := by
  rw [kanAdjointRelativeTracedEvaluationTriangle, SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm]
  exact Equiv.symm_apply_apply _ _

end SerrePositivity.KST.Spectra.RawSpectrumMapping
