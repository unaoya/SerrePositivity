module
public import SerrePositivity.KST.SConstruction.FullCylinderBoundary
public import SerrePositivity.KST.SConstruction.RelativeSequenceFamilyRectification
public import SerrePositivity.KST.SConstruction.PrescribedRawHomotopyLift

/-! # 両方の全境界を同時に保持する raw 比較の逐次厳密化
概要：入力境界と比較時刻の両端を固定し、零段を変えずに全段比較を厳密に束ねる。
方針：二境界の和の単射を、既存の相対列厳密化のパラメータ境界として使う。
規約：隣接段の全境界固定適合比較は入力。各段の比較の存在だけから供給しない。
使われ方：元の高次 prism による適合比較の到着後、第四辺の全 raw 比較を構成する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open SerrePositivity.SimplicialModel
open SerrePositivity.SimplicialModel.LargeParameterHomotopy
open scoped Simplicial
variable (X : OmegaSpectrum.{u}) (Y : KanSequence.{u})
  {A U : SSet.{u}} (j : A ⟶ U) [Mono j]
  (a b : U ⟶ RawSpectrumMapping.space X Y)
  (H : ∀ n, SSet.Homotopy (a ≫ RawSpectrumMapping.evaluation X Y n)
    (b ≫ RawSpectrumMapping.evaluation X Y n))
  (L : ∀ n, SSet.Homotopy
    ((H (n + 1)).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space)
    ((H n).h ≫ RawSpectrumMapping.step X Y n))
  (hL : ∀ n, (fullCylinderBoundaryInclusion j ▷ (Δ[1] : SSet.{u})) ≫ (L n).h =
    fst (fullCylinderBoundary j) Δ[1] ≫ fullCylinderBoundaryInclusion j ≫
      (H (n + 1)).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space)

/-- 全入力境界と比較時刻の両端を同時に保持して全段を束ねた実 raw 写像。 -/
def fullRelativeRawComparisonMap : U ⊗ (Δ[1] : SSet.{u}) ⟶ RawSpectrumMapping.space X Y :=
  relativeSequenceFamilyRectification X Y (fullCylinderBoundaryInclusion j)
    (fun n => (H n).h) L hL

/-- 各段の全境界は、元の同じ全境界を厳密に回収する。 -/
lemma fullRelativeRawComparisonMap_boundary (n : ℕ) :
    fullCylinderBoundaryInclusion j ≫ fullRelativeRawComparisonMap X Y j a b H L hL ≫
        RawSpectrumMapping.evaluation X Y n = fullCylinderBoundaryInclusion j ≫ (H n).h :=
  relativeSequenceFamilyRectification_boundary _ _ _ _ _ _ n

/-- 比較時刻の両端は全段で元の同じ写像を保持する。 -/
lemma fullRelativeRawComparisonMap_time (n : ℕ) :
    (U ◁ (SSet.boundary 1).ι) ≫ fullRelativeRawComparisonMap X Y j a b H L hL ≫
        RawSpectrumMapping.evaluation X Y n = (U ◁ (SSet.boundary 1).ι) ≫ (H n).h := by
  have he := (fullCylinderBoundary_map_iff j
    (fullRelativeRawComparisonMap X Y j a b H L hL ≫ RawSpectrumMapping.evaluation X Y n)
    (H n).h).mp (fullRelativeRawComparisonMap_boundary X Y j a b H L hL n)
  exact he.1

/-- 入力の全境界も全比較時刻で元の同じ写像を保持する。 -/
lemma fullRelativeRawComparisonMap_input (n : ℕ) :
    (j ▷ (Δ[1] : SSet.{u})) ≫ fullRelativeRawComparisonMap X Y j a b H L hL ≫
        RawSpectrumMapping.evaluation X Y n = (j ▷ (Δ[1] : SSet.{u})) ≫ (H n).h := by
  have he := (fullCylinderBoundary_map_iff j
    (fullRelativeRawComparisonMap X Y j a b H L hL ≫ RawSpectrumMapping.evaluation X Y n)
    (H n).h).mp (fullRelativeRawComparisonMap_boundary X Y j a b H L hL n)
  exact he.2

/-- 元の両 raw 族を両端に持ち、全段を厳密に束ねた実比較円柱。 -/
def fullRelativeRawComparison : SSet.Homotopy a b :=
  familyHomotopyOfBoundary a b (fullRelativeRawComparisonMap X Y j a b H L hL)
    (by
      apply RawSpectrumMapping.hom_ext X Y
      intro n
      rw [Category.assoc, fullRelativeRawComparisonMap_time, familyBoundaryMap_post]
      exact HomotopyEndpointComparison.boundary_eq (H n))

/-- 零段の元の全円柱は変更せず厳密に回収する。 -/
lemma fullRelativeRawComparison_zero :
    (fullRelativeRawComparison X Y j a b H L hL).h ≫ RawSpectrumMapping.evaluation X Y 0 =
      (H 0).h :=
  relativeSequenceFamilyRectification_zero _ _ _ _ _ _

/-- 元の各段からの補正は、両全境界を固定した実ホモトピーの有限列。 -/
lemma fullRelativeRawComparison_chain (n : ℕ) :
    Nonempty (RelativeFamilyChain (fullCylinderBoundaryInclusion j) (H n).h
      ((fullRelativeRawComparison X Y j a b H L hL).h ≫
        RawSpectrumMapping.evaluation X Y n)) :=
  relativeSequenceFamilyRectification_chain X Y (fullCylinderBoundaryInclusion j)
    (fun n => (H n).h) L hL n

/-- 入力の全境界を各段で固定する比較族は、厳密化後も同じ全境界を固定する。 -/
lemma fullRelativeRawComparison_relative
    (hr : ∀ n, (j ▷ (Δ[1] : SSet.{u})) ≫ (H n).h =
      fst A Δ[1] ≫ j ≫ a ≫ RawSpectrumMapping.evaluation X Y n) :
    (j ▷ (Δ[1] : SSet.{u})) ≫ (fullRelativeRawComparison X Y j a b H L hL).h =
      fst A Δ[1] ≫ j ≫ a := by
  apply RawSpectrumMapping.hom_ext X Y
  intro n
  change (j ▷ (Δ[1] : SSet.{u})) ≫
      fullRelativeRawComparisonMap X Y j a b H L hL ≫
        RawSpectrumMapping.evaluation X Y n = _
  rw [fullRelativeRawComparisonMap_input, hr n]
  simp only [Category.assoc]

end SerrePositivity.KST.SConstruction
