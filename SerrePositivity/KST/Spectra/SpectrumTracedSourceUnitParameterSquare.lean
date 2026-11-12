module

public import SerrePositivity.KST.Spectra.SpectrumTracedSourceUnitIntervalCoordinates
public import SerrePositivity.KST.Spectra.SpectrumKanAdjointTracedUnitSquare

/-!
概要：源単位の同じ実三角形を、指定境界を保持した全パラメータ正方形へ展開する。
方針：元の合成三角形の正方形へ、同じ前合成作用だけを後合成する。
規約：構造入力の非定数辺を保持。使われ方：源単位と他の段比較の相対貼り合わせ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence)

/-- 同じ源三角形を展開した正方形。対角辺は実際の次段区間の構造制限。 -/
def tracedSourceUnitParameterSquare (n : ℕ) :
    SSet.Homotopy
      (((tracedSourceUnitStageInterval X Y φ (n + 1)).basedPost
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n)
          ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space)).path)
      (((OmegaSpectrum.tracedSignedLoopUnitStepInterval X n).basedPreAction
        (tracedSourceUnitStructureInput X Y φ n) (𝟙 A)).path) where
  h := compositionTriangleSquare (OmegaSpectrum.tracedSignedLoopUnitTriangle X n) ≫
    (tracedSourceUnitStructureAction X Y φ n).right
  h₀ := by
    rw [← Category.assoc, compositionTriangleSquare_zero]
    have he := tracedSourceUnitParameterTriangle_one_stage X Y φ n
    rw [tracedSourceUnitParameterTriangle, ← Category.assoc,
      SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm] at he
    exact he
  h₁ := by
    rw [← Category.assoc, compositionTriangleSquare_one]
    have he := tracedSourceUnitParameterTriangle_zero X Y φ n
    rw [tracedSourceUnitParameterTriangle, ← Category.assoc,
      SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm] at he
    exact he
  rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim

/-- 左辺全体は、元の源単位の構造入力区間の同じ全パラメータ像。 -/
lemma tracedSourceUnitParameterSquare_start (n : ℕ) :
    SquareAdjustment.leftSide ≫ (tracedSourceUnitParameterSquare X Y φ n).h =
      ((OmegaSpectrum.signedLoopUnitStructurePath X n).basedPreAction
        (tracedSourceUnitStructureInput X Y φ n) (𝟙 A)).path := by
  have hf := tracedSourceUnitParameterTriangle_two X Y φ n
  rw [tracedSourceUnitParameterTriangle, ← Category.assoc,
    SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm] at hf
  have hl : SquareAdjustment.leftSide.{u} =
      CartesianMonoidalCategory.lift (stdSimplex.isTerminalObj₀.from _) (𝟙 (Δ[1] : SSet.{u})) ≫
        (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) := by
    apply CartesianMonoidalCategory.hom_ext <;> rfl
  change _ ≫ (compositionTriangleSquare (OmegaSpectrum.tracedSignedLoopUnitTriangle X n) ≫
    (tracedSourceUnitStructureAction X Y φ n).right) = _
  rw [hl, ← Category.assoc, Category.assoc _ _
    (compositionTriangleSquare (OmegaSpectrum.tracedSignedLoopUnitTriangle X n)),
    compositionTriangleSquare_start]
  simp only [Category.assoc]
  rw [hf, ← Category.assoc, lift_snd, Category.id_comp]

/-- 右辺全体は、同じ第二辺の終頂点で一定。 -/
lemma tracedSourceUnitParameterSquare_finish (n : ℕ) :
    SquareAdjustment.rightSide ≫ (tracedSourceUnitParameterSquare X Y φ n).h =
      SSet.const (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫
        ((OmegaSpectrum.tracedSignedLoopUnitStepInterval X n).basedPreAction
          (tracedSourceUnitStructureInput X Y φ n) (𝟙 A)).path)) := by
  change _ ≫ (compositionTriangleSquare (OmegaSpectrum.tracedSignedLoopUnitTriangle X n) ≫
    (tracedSourceUnitStructureAction X Y φ n).right) = _
  rw [← Category.assoc, compositionTriangleSquare_rightSide, SSet.const_comp]
  have he := tracedSourceUnitParameterTriangle_zero X Y φ n
  rw [tracedSourceUnitParameterTriangle, ← Category.assoc,
    SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm] at he
  have hv := congrArg (fun F => SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ F)) he
  rw [← Category.assoc, SSet.Edge.δ_zero_yonedaEquiv_symm,
    SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at hv
  exact congrArg SSet.const hv

end SerrePositivity.KST.Spectra.RawSpectrumMapping
