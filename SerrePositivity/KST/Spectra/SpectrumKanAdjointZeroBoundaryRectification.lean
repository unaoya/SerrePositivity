module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointZeroBoundaryStructure

/-!
概要：零境界を持つ元の Hom 族の Kan 随伴比較を、同じ境界を保持して全列で厳密化する。
方針：実証済みの垂直構造区間を相対厳密化へ入力し、全評価を元の Kan 随伴へ照合する。
規約：任意の単射パラメータ・零境界。使われ方：基点つき球面族の符号付き loop 比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A B : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence) (j : B ⟶ A) [Mono j.right] (hzero : j ≫ φ = 0)
include hzero

omit [Mono j.right] in
lemma kanAdjointZeroBoundaryProjectionCondition (n : ℕ) :
    kanAdjointParameterStage X Y φ n ≫
      (KanSequence.mappingPre j (KanSequence.signedLoopTail Y.toKanSequence)).app n =
      (homOfParameterFamily X (KanSequence.signedLoopTail Y.toKanSequence) B 0).app n :=
  (kanAdjointParameterStage_zero_boundary X Y φ j hzero n).trans
    (homOfParameterFamily_zero_app X (KanSequence.signedLoopTail Y.toKanSequence) B n).symm

omit [Mono j.right] in
lemma kanAdjointZeroBoundaryStructureCondition (n : ℕ) :
    PointedMapping.VerticalChain
      ((KanSequence.mappingPre j (KanSequence.signedLoopTail Y.toKanSequence)).app (n + 1))
      (X.sigma n ≫ kanAdjointParameterStage X Y φ (n + 1))
      (PointedSimplicialSet.circle.{u} ◁ kanAdjointParameterStage X Y φ n ≫
        (KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).sigma n) :=
  Relation.ReflTransGen.single ⟨kanAdjointParameter_zero_boundary_structurePath X Y φ j hzero n⟩

/-- 元の零境界を保持した、実際の符号付き loop 列への全パラメータ比較。 -/
def kanAdjointZeroBoundaryComparison :
    A ⟶ pointedSpace X (KanSequence.signedLoopTail Y.toKanSequence) :=
  rectifyParameterRelative X (KanSequence.signedLoopTail Y.toKanSequence) j 0
    (kanAdjointParameterStage X Y φ) (kanAdjointZeroBoundaryProjectionCondition X Y φ j hzero)
    (kanAdjointZeroBoundaryStructureCondition X Y φ j hzero)

/-- 元の指定した部分パラメータ上の零族を、全列・全単体で厳密に保持する。 -/
lemma kanAdjointZeroBoundaryComparison_boundary :
    j ≫ kanAdjointZeroBoundaryComparison X Y φ j hzero = 0 :=
  rectifyParameterRelative_boundary X (KanSequence.signedLoopTail Y.toKanSequence) j 0
    (kanAdjointParameterStage X Y φ) (kanAdjointZeroBoundaryProjectionCondition X Y φ j hzero)
    (kanAdjointZeroBoundaryStructureCondition X Y φ j hzero)

/-- 元の各段の全パラメータ座標は、元の同じ族の Kan 随伴への後合成と同じ成分。 -/
lemma kanAdjointZeroBoundaryComparison_evaluation_component (n : ℕ) :
    PointedMapping.componentOf (kanAdjointZeroBoundaryComparison X Y φ j hzero ≫
      pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n) =
      PointedMapping.componentOf (φ ≫ kanAdjointParameterLeft X Y n) := by
  have h := rectifyParameterRelative_evaluation_component X
    (KanSequence.signedLoopTail Y.toKanSequence) j 0 (kanAdjointParameterStage X Y φ)
    (kanAdjointZeroBoundaryProjectionCondition X Y φ j hzero)
    (kanAdjointZeroBoundaryStructureCondition X Y φ j hzero) n
  rw [kanAdjointParameterStage, PointedMapping.transpose_transpose] at h
  exact h

/-- 各段の修正は、元のパラメータの基点を固定する実際のホモトピーで比較できる。 -/
lemma kanAdjointZeroBoundaryComparison_evaluation_homotopy (n : ℕ) :
    ∃ H : SSet.Homotopy (kanAdjointZeroBoundaryComparison X Y φ j hzero ≫
        pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n).right
        (φ ≫ kanAdjointParameterLeft X Y n).right,
      A.hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ (kanAdjointParameterTarget X Y n).hom := by
  let coordinateKan : KanComplex (kanAdjointParameterTarget X Y n).right :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
  exact (PointedMapping.piZero_eq_iff_pointedHomotopy _ _).1
    (kanAdjointZeroBoundaryComparison_evaluation_component X Y φ j hzero n)

/-- 元の零段の Kan 随伴座標は、零境界を保持した厳密化でも厳密に保持する。 -/
lemma kanAdjointZeroBoundaryComparison_evaluation_zero :
    kanAdjointZeroBoundaryComparison X Y φ j hzero ≫
      pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) 0 =
      φ ≫ kanAdjointParameterLeft X Y 0 := by
  exact (rectifyParameterRelative_evaluation_zero X (KanSequence.signedLoopTail Y.toKanSequence)
    j 0 (kanAdjointParameterStage X Y φ) (kanAdjointZeroBoundaryProjectionCondition X Y φ j hzero)
    (kanAdjointZeroBoundaryStructureCondition X Y φ j hzero)).trans
      (PointedMapping.transpose_transpose _)

end SerrePositivity.KST.Spectra.RawSpectrumMapping
