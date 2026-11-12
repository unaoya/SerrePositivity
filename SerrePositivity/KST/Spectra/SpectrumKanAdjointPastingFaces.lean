module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointTracedTriangleFaces
public import SerrePositivity.KST.Spectra.SpectrumKanAdjointAdjustedTransport
public import SerrePositivity.KST.Spectra.RelativeTracedPathFormulas

/-!
概要：元の輸送正方形と相対帰納正方形の上下の辺を、指定した同じ二つの合成三角形へ照合する。
方針：名前つき段区間の三辺の式と、元の帰納区間の制限・構造像の公式だけを使う。
規約：三角形や区間を選び直さない。使われ方：元の二正方形の指定三角形つき合成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A B : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence) (j : B ⟶ A) [Mono j.right]

/-- 輸送正方形の始辺は、下側に指定した同じ三角形の第一辺。 -/
lemma kanAdjointAdjustedTransport_source_face (n : ℕ) :
    SSet.ι₀ ≫ (kanAdjointCanonicalAdjustedTransport X Y φ j n).h =
      stdSimplex.δ (2 : Fin 3) ≫ kanAdjointRelativeTracedSourceTriangle X Y φ j n := by
  rw [kanAdjointRelativeTracedSourceTriangle_two]
  exact (kanAdjointCanonicalAdjustedTransport X Y φ j n).h₀.trans
    (PointedMapping.VerticalPath.edge_yonedaEquiv_symm _)

/-- 輸送正方形の終辺も、上側に指定した同じ三角形の第一辺。 -/
lemma kanAdjointAdjustedTransport_target_face (n : ℕ) :
    SSet.ι₁ ≫ (kanAdjointCanonicalAdjustedTransport X Y φ j n).h =
      stdSimplex.δ (2 : Fin 3) ≫ kanAdjointRelativeTracedTargetTriangle X Y φ j n := by
  rw [kanAdjointRelativeTracedTargetTriangle_two]
  exact (kanAdjointCanonicalAdjustedTransport X Y φ j n).h₁.trans
    (PointedMapping.VerticalPath.edge_yonedaEquiv_symm _)

/-- 相対帰納正方形の始辺は、下側に指定した同じ三角形の第二辺。 -/
lemma kanAdjointRelativeStructure_source_face (n : ℕ) :
    SSet.ι₀ ≫ (kanAdjointRelativeTracedStructureHomotopy X Y φ j n).h =
      stdSimplex.δ (0 : Fin 3) ≫ kanAdjointRelativeTracedSourceTriangle X Y φ j n := by
  rw [kanAdjointRelativeTracedSourceTriangle_zero]
  have ht := KanSequence.relativeTracedRestrictionPath_pre (X := X.toKanSequence)
    (Y := KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence))
    (Z := KanSequence.mapping B (KanSequence.signedLoopTail Y.toKanSequence))
    X.sigma_mono (KanSequence.mappingPre j (KanSequence.signedLoopTail Y.toKanSequence))
    (mappingPre_level_horn_rlp j (KanSequence.signedLoopTail Y.toKanSequence))
    (homOfParameterFamily X (KanSequence.signedLoopTail Y.toKanSequence) B
      (kanAdjointTracedBoundary X Y φ j))
    (fun n ↦ (kanAdjointTracedBoundaryCoordinate X Y φ j n).stage)
    (fun n ↦ (kanAdjointTracedBoundaryCoordinate X Y φ j n).projection)
    (kanAdjointCanonicalVerticalStructurePath X Y φ j) n
  have ho := (kanAdjointRelativeTracedStructureHomotopy X Y φ j n).h₀.trans
    ((PointedMapping.VerticalPath.edge_yonedaEquiv_symm _).trans ht)
  have he := congrArg (· ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n)
    ((KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).level
      (n + 1)).space).right)
    (kanAdjointRelativeTracedStageCorrectionInterval_path X Y φ j (n + 1))
  exact ho.trans he.symm

/-- 相対帰納正方形の終辺も、上側に指定した同じ三角形の第二辺。 -/
lemma kanAdjointRelativeStructure_target_face (n : ℕ) :
    SSet.ι₁ ≫ (kanAdjointRelativeTracedStructureHomotopy X Y φ j n).h =
      stdSimplex.δ (0 : Fin 3) ≫ kanAdjointRelativeTracedTargetTriangle X Y φ j n := by
  rw [kanAdjointRelativeTracedTargetTriangle_zero]
  let q := KanSequence.mappingPre j (KanSequence.signedLoopTail Y.toKanSequence)
  let b := homOfParameterFamily X (KanSequence.signedLoopTail Y.toKanSequence) B
    (kanAdjointTracedBoundary X Y φ j)
  let f := fun n ↦ (kanAdjointTracedBoundaryCoordinate X Y φ j n).stage
  let hb := fun n ↦ (kanAdjointTracedBoundaryCoordinate X Y φ j n).projection
  let h := kanAdjointCanonicalVerticalStructurePath X Y φ j
  let s := KanSequence.relativeTracedStage X.sigma_mono q
    (mappingPre_level_horn_rlp j (KanSequence.signedLoopTail Y.toKanSequence)) b f hb h n
  have ht := KanSequence.relativeTracedStepPath_path (X := X.toKanSequence)
    (Y := KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence))
    (Z := KanSequence.mapping B (KanSequence.signedLoopTail Y.toKanSequence)) q b f n s
  have ho := (kanAdjointRelativeTracedStructureHomotopy X Y φ j n).h₁.trans
    ((PointedMapping.VerticalPath.edge_yonedaEquiv_symm _).trans ht)
  have he := congrArg (fun P ↦ P ≫
      (suspensionHom (X.level n).space
        ((KanSequence.mapping A
          (KanSequence.signedLoopTail Y.toKanSequence)).level n).space).right ≫
      (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
        ((KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).sigma n)).right)
    (kanAdjointRelativeTracedStageCorrectionInterval_path X Y φ j n)
  exact ho.trans he.symm

end SerrePositivity.KST.Spectra.RawSpectrumMapping
