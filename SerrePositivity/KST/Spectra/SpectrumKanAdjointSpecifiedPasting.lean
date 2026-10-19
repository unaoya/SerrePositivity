module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointPastingFaces
public import SerrePositivity.KST.Spectra.SpecifiedSquarePasting

/-!
概要：元の Kan 随伴の段調整と相対修正の正方形を、同じ上下の合成三角形を保って貼る。
方針：厳密に同じ共通辺を使い、指定二単体族の上で指数写像空間の内ホーンを充填する。
規約：元の構造区間は始点境界に残る。使われ方：全列区間の構造比較への次元ごとの接続。
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

/-- 同じ共通辺を始辺に持つ、相対帰納正方形の左右方向の実ホモトピー。 -/
def kanAdjointTracedPastingSecond (n : ℕ) :
    SSet.Homotopy
      (SquareAdjustment.rightSide ≫ (kanAdjointCanonicalAdjustedTransport X Y φ j n).h)
      (SquareAdjustment.rightSide ≫ (kanAdjointRelativeTracedStructureHomotopy X Y φ j n).h) where
  h := (β_ (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).hom ≫
    (kanAdjointRelativeTracedStructureHomotopy X Y φ j n).h
  h₀ := (SquareAdjustment.flip (kanAdjointRelativeTracedStructureHomotopy X Y φ j n)).h₀.trans
    (kanAdjointCanonicalAdjustedTransport_relative_seam X Y φ j n).symm
  h₁ := (SquareAdjustment.flip (kanAdjointRelativeTracedStructureHomotopy X Y φ j n)).h₁
  rel := by ext m ⟨⟨s, hs⟩, r⟩; exact hs.elim

/-- 元の二正方形を、名前つきの同じ上下の実合成三角形を保持して貼る。 -/
def kanAdjointRelativeTracedPastingComposite (n : ℕ) :=
  SquareAdjustment.SpecifiedPasting.choose
    (SquareAdjustment.flip (kanAdjointCanonicalAdjustedTransport X Y φ j n))
    (kanAdjointTracedPastingSecond X Y φ j n)
    (kanAdjointRelativeTracedSourceTriangle X Y φ j n)
    (kanAdjointRelativeTracedTargetTriangle X Y φ j n)
    ((SquareAdjustment.leftSide_swap _).trans
      (kanAdjointAdjustedTransport_source_face X Y φ j n))
    ((SquareAdjustment.rightSide_swap _).trans
      (kanAdjointAdjustedTransport_target_face X Y φ j n))
    ((SquareAdjustment.leftSide_swap _).trans
      (kanAdjointRelativeStructure_source_face X Y φ j n))
    ((SquareAdjustment.rightSide_swap _).trans
      (kanAdjointRelativeStructure_target_face X Y φ j n))

/-- 指定した上下の同じ三角形の対角辺を両端に持つ、元の二正方形の実合成。 -/
def kanAdjointRelativeTracedPastedSquare (n : ℕ) :=
  SquareAdjustment.SpecifiedPasting.squareHomotopy _ _ _ _
    (kanAdjointRelativeTracedPastingComposite X Y φ j n)

/-- 合成後の区間族は、元の名前つき段区間の制限と構造像の間の実ホモトピーを持つ。 -/
def kanAdjointRelativeTracedEvaluationStructureHomotopy (n : ℕ) :
    SSet.Homotopy
      ((kanAdjointRelativeTracedStageEvaluationInterval X Y φ j (n + 1)).pre (X.sigma n)).path
      ((kanAdjointRelativeTracedStageEvaluationInterval
          X Y φ j n).suspension.forgetProjection.basedPost
        ((KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).sigma n)).path where
  h := (kanAdjointRelativeTracedPastedSquare X Y φ j n).h
  h₀ := (kanAdjointRelativeTracedPastedSquare X Y φ j n).h₀.trans
    (kanAdjointRelativeTracedSourceTriangle_one X Y φ j n)
  h₁ := (kanAdjointRelativeTracedPastedSquare X Y φ j n).h₁.trans
    (kanAdjointRelativeTracedTargetTriangle_one X Y φ j n)
  rel := by ext m ⟨⟨s, hs⟩, r⟩; exact hs.elim

/-- 合成正方形の左辺は、三辺を保持した元の輸送正方形の左辺そのもの。 -/
lemma kanAdjointRelativeTracedPastedSquare_left (n : ℕ) :
    SquareAdjustment.leftSide ≫ (kanAdjointRelativeTracedPastedSquare X Y φ j n).h =
      SquareAdjustment.leftSide ≫ (kanAdjointCanonicalAdjustedTransport X Y φ j n).h :=
  SquareAdjustment.SpecifiedPasting.square_left _ _ _ _ _

/-- 合成正方形の右辺も、同じ元の相対帰納正方形の右辺そのもの。 -/
lemma kanAdjointRelativeTracedPastedSquare_right (n : ℕ) :
    SquareAdjustment.rightSide ≫ (kanAdjointRelativeTracedPastedSquare X Y φ j n).h =
      SquareAdjustment.rightSide ≫ (kanAdjointRelativeTracedStructureHomotopy X Y φ j n).h :=
  SquareAdjustment.SpecifiedPasting.square_right _ _ _ _ _

end SerrePositivity.KST.Spectra.RawSpectrumMapping
