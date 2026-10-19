module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointStageDifferenceFreeStructure
public import SerrePositivity.KST.Spectra.RawSpectrumStrictParameterHomotopy

/-!
概要：共有辺で比較した元の相対厳密化と単位後合成を、元の全 Hom の実ホモトピーで結ぶ。
方針：自由境界上に垂直な構造区間を全列の相対厳密化へ渡し、同じ全列区間を回収する。
規約：段ごとの成分だけから推論しない。使われ方：元の比較への単位後合成の同値性の移送。
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

/-- 元の二つの厳密な列射を両端に保つ、実際の全列区間。 -/
def kanAdjointStageDifferenceStrictInterval :
    KanSequence.StrictInterval (kanAdjointRelativeTracedParameterHom X Y φ j)
      (kanAdjointTracedUnitParameterHom X Y φ) :=
  KanSequence.rectifyInterval (X := X.toKanSequence)
    (Y := KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)) X.sigma_mono
    (kanAdjointRelativeTracedParameterHom X Y φ j) (kanAdjointTracedUnitParameterHom X Y φ)
    (kanAdjointStageDifferenceFreeMap X Y φ j)
    (kanAdjointStageDifferenceFreeMap_boundary X Y φ j)
    (kanAdjointStageDifferenceFreeStructureInterval X Y φ j)

/-- 元の全 Hom の相対比較族は、同じ単位後合成の族と実際の基点固定ホモトピーで結ばれる。 -/
lemma kanAdjointRelativeTracedComparison_unit_homotopy :
    ∃ H : SSet.Homotopy (kanAdjointRelativeTracedComparison X Y φ j).right
        (kanAdjointTracedUnitFamily X Y φ).right,
      A.hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫
          (pointedSpace X (KanSequence.signedLoopTail Y.toKanSequence)).hom := by
  have hex : ∃ H : SSet.Homotopy (kanAdjointRelativeTracedComparison X Y φ j).right
      (parameterFamily X (KanSequence.signedLoopTail Y.toKanSequence) A
        (kanAdjointTracedUnitParameterHom X Y φ)).right,
      A.hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫
          (pointedSpace X (KanSequence.signedLoopTail Y.toKanSequence)).hom :=
    ⟨strictParameterHomotopy X (KanSequence.signedLoopTail Y.toKanSequence) A
      (kanAdjointStageDifferenceStrictInterval X Y φ j),
      strictParameterHomotopy_base X (KanSequence.signedLoopTail Y.toKanSequence) A
        (kanAdjointStageDifferenceStrictInterval X Y φ j)⟩
  have ht : parameterFamily X (KanSequence.signedLoopTail Y.toKanSequence) A
      (kanAdjointTracedUnitParameterHom X Y φ) = kanAdjointTracedUnitFamily X Y φ :=
    parameterFamily_homOfParameterFamily X (KanSequence.signedLoopTail Y.toKanSequence) A
      (kanAdjointTracedUnitFamily X Y φ)
  rw [ht] at hex
  exact hex

end SerrePositivity.KST.Spectra.RawSpectrumMapping
