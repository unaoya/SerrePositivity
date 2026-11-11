module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointStageDifferenceStrictInterval
public import SerrePositivity.KST.Spectra.RawSpectrumPointedMappingWhitehead
public import SerrePositivity.KST.Spectra.RawSpectrumMappingAcyclic
public import SerrePositivity.KST.Spectra.SpectrumKanAdjointRelativeTracedBFComparison

/-!
概要：元の全 Hom の相対トレース付き比較は、入力族が全基点 π 同型なら全基点 π 同型。
方針：全列区間から得た実ホモトピーで、単位後合成と射影の同型性を移す。
規約：全 Hom の実写像を検査。使われ方：元の evaluationPost の比較への接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u})

/-- 同じトレース付き単位の後合成は、元の BF Hom 全体で全基点 π 同型。 -/
lemma tracedSignedLoopUnit_post_piIsomorphism :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (pointedPost X
      (OmegaSpectrum.sequenceHom (OmegaSpectrum.tracedSignedLoopUnit Y))).right := by
  exact pointedPost_piIsomorphism_of_levelwise X
    (OmegaSpectrum.tracedSignedLoopUnit Y) (OmegaSpectrum.tracedSignedLoopUnit_levelwise Y)

variable {A B : PointedSimplicialSet.{u}} [KanComplex A.right]
  (φ : A ⟶ pointedSpace X Y.toKanSequence) (j : B ⟶ A) [Mono j.right]

/-- 元の入力族が π 同型なら、単位後合成の族も全基点 π 同型。 -/
lemma kanAdjointTracedUnitFamily_piIsomorphism (hφ : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism φ.right) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (kanAdjointTracedUnitFamily X Y φ).right := by
  have hp := post_piIsomorphism X (OmegaSpectrum.signedLoopProjection Y)
    (signedLoopProjection_level_rlp Y)
  exact hφ.comp ((tracedSignedLoopUnit_post_piIsomorphism X Y).comp hp)

/-- 元の全 Hom の相対比較そのものも、全基点 π 同型。 -/
lemma kanAdjointRelativeTracedComparison_piIsomorphism (hφ : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism φ.right) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (kanAdjointRelativeTracedComparison X Y φ j).right := by
  obtain ⟨H, _⟩ := kanAdjointRelativeTracedComparison_unit_homotopy X Y φ j
  exact (kanPiIsomorphism_iff_of_homotopy H).mpr
    (kanAdjointTracedUnitFamily_piIsomorphism X Y φ hφ)

/-- BF 模型へ持ち上げた同じ全 Hom 比較も、射影の全単射 RLP を打ち消して π 同型。 -/
lemma kanAdjointRelativeTracedBFComparison_piIsomorphism (hφ : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism φ.right) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (kanAdjointRelativeTracedBFComparison X Y φ j).right := by
  have hp := post_piIsomorphism X (OmegaSpectrum.signedLoopProjection Y)
    (signedLoopProjection_level_rlp Y)
  apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp (g :=
    (pointedPost X (OmegaSpectrum.signedLoopProjection Y)).right) _ hp
  rw [← Under.comp_right, kanAdjointRelativeTracedBFComparison_projection]
  exact kanAdjointRelativeTracedComparison_piIsomorphism X Y φ j hφ

end SerrePositivity.KST.Spectra.RawSpectrumMapping
