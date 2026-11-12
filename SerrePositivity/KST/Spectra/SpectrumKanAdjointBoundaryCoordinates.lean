module

public import SerrePositivity.KST.Spectra.PointedHomotopyExtension
public import SerrePositivity.KST.Spectra.SpectrumKanAdjointZeroBoundaryStructure

/-!
概要：非零境界の指定された比較ホモトピーを保ち、元の Kan 随伴の段座標を調整する。
方針：単射と区間端点の pushout-product の充填で境界比較を延長し、同じ段射を転置する。
規約：境界ホモトピーを入力する。使われ方：非零境界の相対厳密化の段射の構成。
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
  (φ : A ⟶ pointedSpace X Y.toKanSequence) (j : B ⟶ A)
  (c : B ⟶ pointedSpace X (KanSequence.signedLoopTail Y.toKanSequence))

/-- 指定された非零境界の段座標との、元の点つき比較ホモトピー。 -/
abbrev KanAdjointBoundaryHomotopy (n : ℕ) :=
  SSet.Homotopy (j.right ≫ (φ ≫ kanAdjointParameterLeft X Y n).right)
    (c ≫ pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n).right

/-- 調整済み段座標と、入力された境界区間そのものを保つ実際の比較区間。 -/
structure KanAdjointBoundaryCoordinate (n : ℕ)
    (H : KanAdjointBoundaryHomotopy X Y φ j c n) where
  coordinate : A ⟶ kanAdjointParameterTarget X Y n
  boundary : j ≫ coordinate =
    c ≫ pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n
  comparison : SSet.Homotopy (φ ≫ kanAdjointParameterLeft X Y n).right coordinate.right
  comparison_base : A.hom ▷ (Δ[1] : SSet.{u}) ≫ comparison.h =
    toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ (kanAdjointParameterTarget X Y n).hom
  comparison_boundary : j.right ▷ (Δ[1] : SSet.{u}) ≫ comparison.h = H.h

/-- 指定した非零境界の比較区間を、同じ始点から全パラメータへ延長する。 -/
def kanAdjointBoundaryCoordinate [Mono j.right] (n : ℕ)
    (H : KanAdjointBoundaryHomotopy X Y φ j c n)
    (hb : B.hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
      toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ (kanAdjointParameterTarget X Y n).hom) :
    KanAdjointBoundaryCoordinate X Y φ j c n H := by
  let parameterTargetKan : KanComplex (kanAdjointParameterTarget X Y n).right :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
  let ex := PointedExtension.exists_homotopy_from_zero j
    (φ ≫ kanAdjointParameterLeft X Y n)
    (c ≫ pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n) H hb
  exact ⟨ex.choose, ex.choose_spec.1, ex.choose_spec.2.choose,
    ex.choose_spec.2.choose_spec.1, ex.choose_spec.2.choose_spec.2⟩

namespace KanAdjointBoundaryCoordinate
variable {X Y φ j c} {n : ℕ} {H : KanAdjointBoundaryHomotopy X Y φ j c n}

/-- 調整前後の元の座標は、選んだ比較区間により同じ成分を持つ。 -/
lemma component (s : KanAdjointBoundaryCoordinate X Y φ j c n H) :
    PointedMapping.componentOf s.coordinate =
      PointedMapping.componentOf (φ ≫ kanAdjointParameterLeft X Y n) :=
  (π₀.sound (PointedMapping.edgeOfHomotopy s.comparison s.comparison_base)).symm

/-- 調整済みの座標を転置した、cotensor 値の段射。 -/
def stage (s : KanAdjointBoundaryCoordinate X Y φ j c n H) :
    (X.level n).space ⟶
      (ihom A).obj ((KanSequence.signedLoopTail Y.toKanSequence).level n).space :=
  PointedMapping.transpose s.coordinate

/-- 転置した段射は、指定された元の非零境界族の段へ厳密に射影される。 -/
lemma projection (s : KanAdjointBoundaryCoordinate X Y φ j c n H) :
    s.stage ≫ (KanSequence.mappingPre j (KanSequence.signedLoopTail Y.toKanSequence)).app n =
      (homOfParameterFamily X (KanSequence.signedLoopTail Y.toKanSequence) B c).app n := by
  have h := PointedMapping.transpose_pre_outer s.coordinate j
  have hc := congrArg PointedMapping.transpose s.boundary
  have he := congrArg PointedMapping.transpose
    (homOfParameterFamily_transpose_evaluation X
      (KanSequence.signedLoopTail Y.toKanSequence) B c n)
  rw [PointedMapping.transpose_transpose] at he
  exact h.symm.trans (hc.trans he.symm)

/-- 転置した段射も、元の Kan 随伴の段射と同じ成分を持つ。 -/
lemma stage_component (s : KanAdjointBoundaryCoordinate X Y φ j c n H) :
    PointedMapping.componentOf s.stage =
      PointedMapping.componentOf (kanAdjointParameterStage X Y φ n) :=
  PointedMapping.componentOf_transpose s.component

end KanAdjointBoundaryCoordinate
end SerrePositivity.KST.Spectra.RawSpectrumMapping
