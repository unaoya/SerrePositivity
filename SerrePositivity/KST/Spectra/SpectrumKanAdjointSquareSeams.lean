module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointTransportSquares
public import SerrePositivity.KST.Spectra.SpectrumKanAdjointStructureDeformation
public import SerrePositivity.KST.Spectra.SpectrumKanAdjointRelativeTracedSquares

/-!
概要：段調整の輸送正方形と相対厳密化の正方形を、同じ選択済み垂直化の実変形でつなぐ。
方針：元の収縮持ち上げから変形を回収し、その両辺を二つの正方形の元の境界へ照合する。
規約：区間の類から貼り合わせを仮定しない。使われ方：全列区間の構造比較の実充填。
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

/-- 元の輸送辺から、相対帰納構成に使った同じ垂直構造区間への両端固定変形。 -/
def kanAdjointCanonicalStructureDeformation (n : ℕ) :=
  kanAdjointBoundaryStructureDeformation X Y φ j (kanAdjointTracedBoundary X Y φ j)
    (kanAdjointTracedBoundaryHomotopy X Y φ j) (kanAdjointTracedBoundaryCoordinate X Y φ j) n
    (kanAdjointCanonicalStageStructurePath X Y φ j n)
    (kanAdjointCanonicalStructureContraction X Y φ j n)

/-- 垂直化の実変形は、元の二つの端点を全区間で厳密に固定する。 -/
lemma kanAdjointCanonicalStructureDeformation_boundary (n : ℕ) :
    (boundary 1).ι ▷ (Δ[1] : SSet.{u}) ≫
        (kanAdjointCanonicalStructureDeformation X Y φ j n).val.h =
      fst (∂Δ[1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (boundary 1).ι ≫
        (kanAdjointCanonicalStageStructurePath X Y φ j n).path :=
  (kanAdjointCanonicalStructureDeformation X Y φ j n).property.1

/-- 変形全体の非零境界への射影は、元の選択済み収縮そのもの。 -/
lemma kanAdjointCanonicalStructureDeformation_projection (n : ℕ) :
    (kanAdjointCanonicalStructureDeformation X Y φ j n).val.h ≫
      (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
        ((KanSequence.mappingPre j (KanSequence.signedLoopTail Y.toKanSequence)).app
          (n + 1))).right =
      (kanAdjointCanonicalStructureContraction X Y φ j n).homotopy.h :=
  (kanAdjointCanonicalStructureDeformation X Y φ j n).property.2

/-- 輸送正方形の右辺は、同じ実変形の始辺そのものとして貼れる。 -/
lemma kanAdjointCanonicalStructureDeformation_transport_seam (n : ℕ) :
    stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u}) ≫
        kanAdjointCanonicalTransportSquare X Y φ j n =
      snd (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ SSet.ι₀ ≫
        (kanAdjointCanonicalStructureDeformation X Y φ j n).val.h := by
  rw [(kanAdjointCanonicalStructureDeformation X Y φ j n).val.h₀]
  exact kanAdjointCanonicalTransportSquare_finish X Y φ j n

/-- 相対帰納正方形の左辺も、同じ実変形の終辺そのものとして貼れる。 -/
lemma kanAdjointCanonicalStructureDeformation_relative_seam (n : ℕ) :
    stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u}) ≫
        (kanAdjointRelativeTracedStructureHomotopy X Y φ j n).h =
      snd (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ SSet.ι₁ ≫
        (kanAdjointCanonicalStructureDeformation X Y φ j n).val.h := by
  rw [(kanAdjointCanonicalStructureDeformation X Y φ j n).val.h₁]
  exact kanAdjointRelativeTracedStructureHomotopy_start X Y φ j n

end SerrePositivity.KST.Spectra.RawSpectrumMapping
