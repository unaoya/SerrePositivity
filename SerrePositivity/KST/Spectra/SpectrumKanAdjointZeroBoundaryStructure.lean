module

public import SerrePositivity.KST.Spectra.SignedLoopUnitStructurePath
public import SerrePositivity.KST.Spectra.PointedRelativeTransposePaths
public import SerrePositivity.KST.Spectra.SpectrumKanAdjointParameterStructurePaths
public import SerrePositivity.KST.Spectra.SequenceParameterRelativeRectification

/-!
概要：零境界を持つ元の Hom 族の Kan 随伴の構造比較を、指定制限の上で垂直な区間で構成する。
方針：逆向きの比較区間を係数空間で一度選び、零境界の入力へ前合成して同じ区間を転置する。
規約：一般の非零境界へ一般化しない。使われ方：基点つき球面族の実際の相対厳密化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- 元の零パラメータ族から回収した列射の全ての段も零。 -/
lemma homOfParameterFamily_zero_app (X : OmegaSpectrum.{u}) (Y : KanSequence.{u})
    (B : PointedSimplicialSet.{u}) (n : ℕ) :
    (homOfParameterFamily X Y B 0).app n = 0 := by
  have ht := homOfParameterFamily_transpose_evaluation X Y B 0 n
  rw [zero_comp] at ht
  have h := congrArg PointedMapping.transpose ht
  rw [PointedMapping.transpose_transpose, PointedMapping.transpose_zero] at h
  exact h

/-- 元の Kan 随伴への後合成を転置した、任意の元の全 Hom パラメータ族の段射。 -/
def kanAdjointParameterStage (X Y : OmegaSpectrum.{u}) {A : PointedSimplicialSet.{u}}
    (φ : A ⟶ pointedSpace X Y.toKanSequence) (n : ℕ) :
    (X.level n).space ⟶
      (ihom A).obj ((KanSequence.signedLoopTail Y.toKanSequence).level n).space :=
  PointedMapping.transpose (φ ≫ kanAdjointParameterLeft X Y n)

/-- 逆向きの構造比較を係数空間で一度選ぶ。パラメータの部分対象には依存しない。 -/
def kanAdjointCoefficientReversePath (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    PointedMapping.VerticalPath (PointedObject.toPoint
      (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
        ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space))
      ((ihom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)).map
        (Y.sigma n ≫ KanSequence.kanAdjoint Y.toKanSequence (n + 1)))
      ((ihom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)).map
        (PointedSimplicialSet.circle.{u} ◁ KanSequence.kanAdjoint Y.toKanSequence n ≫
          (KanSequence.signedLoopTail Y.toKanSequence).sigma n)) :=
  PointedMapping.VerticalPath.basedIhomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
    (OmegaSpectrum.signedLoopUnitStructurePath Y n)

/-- 零境界を持つ元の族の転置した段射は、同じ指定部分への制限でも厳密に零。 -/
lemma kanAdjointParameterStage_zero_boundary (X Y : OmegaSpectrum.{u})
    {A B : PointedSimplicialSet.{u}} (φ : A ⟶ pointedSpace X Y.toKanSequence) (j : B ⟶ A)
    (hzero : j ≫ φ = 0) (n : ℕ) :
    kanAdjointParameterStage X Y φ n ≫
      (KanSequence.mappingPre j (KanSequence.signedLoopTail Y.toKanSequence)).app n = 0 := by
  have ht := PointedMapping.transpose_pre_outer (φ ≫ kanAdjointParameterLeft X Y n) j
  have hz : j ≫ (φ ≫ kanAdjointParameterLeft X Y n) = 0 := by
    rw [← Category.assoc, hzero, zero_comp]
  have h := congrArg PointedMapping.transpose hz
  rw [PointedMapping.transpose_zero] at h
  exact ht.symm.trans h

/-- 元の零境界を全区間で固定した、Kan 随伴の実際の構造比較の垂直区間。 -/
def kanAdjointParameter_zero_boundary_structurePath (X Y : OmegaSpectrum.{u})
    {A B : PointedSimplicialSet.{u}} (φ : A ⟶ pointedSpace X Y.toKanSequence) (j : B ⟶ A)
    (hzero : j ≫ φ = 0) (n : ℕ) :
    PointedMapping.VerticalPath
      ((KanSequence.mappingPre j (KanSequence.signedLoopTail Y.toKanSequence)).app (n + 1))
      (X.sigma n ≫ kanAdjointParameterStage X Y φ (n + 1))
      (PointedSimplicialSet.circle.{u} ◁ kanAdjointParameterStage X Y φ n ≫
        (KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).sigma n) := by
  let e := φ ≫ (pointedEvaluation X Y.toKanSequence n ≫
    suspensionHom (X.level n).space (Y.level n).space)
  have hz : j ≫ e = 0 := by
    dsimp only [e]
    rw [← Category.assoc, hzero, zero_comp]
  let P := (kanAdjointCoefficientReversePath X Y n).preTransposeOverZero e j hz
  have hr : (φ ≫ kanAdjointParameterLeft X Y (n + 1)) ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n)
        ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space =
      e ≫ (ihom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)).map
        (Y.sigma n ≫ KanSequence.kanAdjoint Y.toKanSequence (n + 1)) := by
    have h := congrArg (φ ≫ ·) (kanAdjointParameterLeft_source_restriction X Y n)
    simp only [e, Category.assoc] at h ⊢
    exact h
  have hl : (φ ≫ kanAdjointParameterLeft X Y n) ≫
      pointedStep X (KanSequence.signedLoopTail Y.toKanSequence) n =
      e ≫ (ihom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)).map
        (PointedSimplicialSet.circle.{u} ◁ KanSequence.kanAdjoint Y.toKanSequence n ≫
          (KanSequence.signedLoopTail Y.toKanSequence).sigma n) := by
    have h := congrArg (φ ≫ ·) (kanAdjointParameterLeft_step X Y n)
    simp only [e, Category.assoc] at h ⊢
    exact h
  have hR := transpose_restriction X (KanSequence.signedLoopTail Y.toKanSequence) A n
    (φ ≫ kanAdjointParameterLeft X Y (n + 1))
  have hL := transpose_step X (KanSequence.signedLoopTail Y.toKanSequence) A n
    (φ ≫ kanAdjointParameterLeft X Y n)
  exact P.changeEndpoints (hR.symm.trans (congrArg PointedMapping.transpose hr))
    (hL.symm.trans (congrArg PointedMapping.transpose hl))

end SerrePositivity.KST.Spectra.RawSpectrumMapping
