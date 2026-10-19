module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointBoundaryStructure
public import SerrePositivity.KST.Spectra.SequenceParameterRelativeHomotopy

/-!
概要：指定された非零境界の比較区間と構造射影の収縮から、実際の全列の比較を構成する。
方針：調整済み段射と、射影収縮を持ち上げた垂直構造区間を既存の相対厳密化へ入力する。
規約：構造射影の二次元収縮は入力として残る。使われ方：全 Hom 比較の相対構成の分解。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A B : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence) (j : B ⟶ A) [Mono j.right]
  (c : B ⟶ pointedSpace X (KanSequence.signedLoopTail Y.toKanSequence))
  (H : ∀ n, KanAdjointBoundaryHomotopy X Y φ j c n)
  (s : ∀ n, KanAdjointBoundaryCoordinate X Y φ j c n (H n))
  (P : ∀ n, KanAdjointBoundaryStructurePath X Y φ j c H s n)
  (K : ∀ n, KanAdjointBoundaryStructureContraction X Y φ j c H s n (P n))

include K in
/-- 指定した射影収縮を持ち上げて得る、実際の垂直構造鎖。 -/
lemma kanAdjointBoundaryStructure_chain (n : ℕ) :
    PointedMapping.VerticalChain
      ((KanSequence.mappingPre j (KanSequence.signedLoopTail Y.toKanSequence)).app (n + 1))
      (X.sigma n ≫ (s (n + 1)).stage)
      (PointedSimplicialSet.circle.{u} ◁ (s n).stage ≫
        (KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).sigma n) := by
  exact .single ⟨kanAdjointBoundaryVerticalStructurePath X Y φ j c H s n (P n) (K n)⟩

/-- 指定非零境界を全列で厳密に保つ、元の全パラメータの Kan 随伴比較。 -/
def kanAdjointBoundaryComparison :
    A ⟶ pointedSpace X (KanSequence.signedLoopTail Y.toKanSequence) :=
  rectifyParameterRelative X (KanSequence.signedLoopTail Y.toKanSequence) j c
    (fun n ↦ (s n).stage) (fun n ↦ (s n).projection)
    (kanAdjointBoundaryStructure_chain X Y φ j c H s P K)

/-- 二次元の入力から構成した全列の比較は、元の指定非零境界そのものへ制限される。 -/
lemma kanAdjointBoundaryComparison_boundary :
    j ≫ kanAdjointBoundaryComparison X Y φ j c H s P K = c :=
  rectifyParameterRelative_boundary X (KanSequence.signedLoopTail Y.toKanSequence) j c
    (fun n ↦ (s n).stage) (fun n ↦ (s n).projection)
    (kanAdjointBoundaryStructure_chain X Y φ j c H s P K)

/-- 構成された全列の各段は、元の Kan 随伴の座標と同じ成分。 -/
lemma kanAdjointBoundaryComparison_evaluation_component (n : ℕ) :
    PointedMapping.componentOf (kanAdjointBoundaryComparison X Y φ j c H s P K ≫
      pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n) =
      PointedMapping.componentOf (φ ≫ kanAdjointParameterLeft X Y n) := by
  have h := rectifyParameterRelative_evaluation_component X
    (KanSequence.signedLoopTail Y.toKanSequence) j c (fun n ↦ (s n).stage)
    (fun n ↦ (s n).projection) (kanAdjointBoundaryStructure_chain X Y φ j c H s P K) n
  rw [KanAdjointBoundaryCoordinate.stage, PointedMapping.transpose_transpose] at h
  exact h.trans (s n).component

/-- 零段の調整済み座標は、全列を厳密化しても変更されない。 -/
lemma kanAdjointBoundaryComparison_evaluation_zero :
    kanAdjointBoundaryComparison X Y φ j c H s P K ≫
      pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) 0 =
      (s 0).coordinate := by
  have h := rectifyParameterRelative_evaluation_zero X
    (KanSequence.signedLoopTail Y.toKanSequence) j c (fun n ↦ (s n).stage)
    (fun n ↦ (s n).projection) (kanAdjointBoundaryStructure_chain X Y φ j c H s P K)
  rw [KanAdjointBoundaryCoordinate.stage, PointedMapping.transpose_transpose] at h
  exact h

end SerrePositivity.KST.Spectra.RawSpectrumMapping
