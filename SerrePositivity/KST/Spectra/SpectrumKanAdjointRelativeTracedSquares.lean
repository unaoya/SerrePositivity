module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointRelativeTracedComparison
public import SerrePositivity.KST.Spectra.SequenceRelativeTracedSquares

/-!
概要：元の非零境界 Kan 随伴比較の実構造三角形を、同じ境界上の実正方形へ展開する。
方針：選択済みの同じ二単体を使い、元の構造区間と正方形全体の厳密射影を保持する。
規約：新しい構造ホモトピーを入力しない。使われ方：全列区間の構造比較の貼り合わせ。
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

/-- 同じ実構造三角形から得る、次段修正の制限と前段修正の構造像の実ホモトピー。 -/
def kanAdjointRelativeTracedStructureHomotopy (n : ℕ) :=
  compositionTriangleHomotopy (kanAdjointRelativeTracedTriangle X Y φ j n)

/-- 正方形の上側には、元の選択済み実構造三角形そのものを保持する。 -/
lemma kanAdjointRelativeTracedStructureHomotopy_upper (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper ≫ (kanAdjointRelativeTracedStructureHomotopy X Y φ j n).h =
      SSet.yonedaEquiv.symm (kanAdjointRelativeTracedTriangle X Y φ j n).simplex :=
  compositionTriangleSquare_upper _

/-- 正方形の始点境界は、調整済み段射の元の実垂直構造区間そのもの。 -/
lemma kanAdjointRelativeTracedStructureHomotopy_start (n : ℕ) :
    stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u}) ≫
        (kanAdjointRelativeTracedStructureHomotopy X Y φ j n).h =
      snd (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫
        (kanAdjointCanonicalVerticalStructurePath X Y φ j n).path := by
  change _ ≫ compositionTriangleSquare (kanAdjointRelativeTracedTriangle X Y φ j n) = _
  rw [compositionTriangleSquare_start]
  exact congrArg (_ ≫ ·) (Equiv.symm_apply_apply _ _)

/-- 元の非零境界への射影は、正方形全体で同じ構造射の定数族になる。 -/
lemma kanAdjointRelativeTracedStructureHomotopy_over (n : ℕ) :
    (kanAdjointRelativeTracedStructureHomotopy X Y φ j n).h ≫
      (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
        ((KanSequence.mappingPre j (KanSequence.signedLoopTail Y.toKanSequence)).app
          (n + 1))).right =
      SSet.const (PointedMapping.familyVertex (X.sigma n ≫
        (homOfParameterFamily X (KanSequence.signedLoopTail Y.toKanSequence) B
          (kanAdjointTracedBoundary X Y φ j)).app (n + 1))) := by
  apply compositionTriangleSquare_post_const
  exact KanSequence.relativeTracedComparison_triangle_over (X := X.toKanSequence)
    (Y := KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence))
    (Z := KanSequence.mapping B (KanSequence.signedLoopTail Y.toKanSequence))
    X.sigma_mono (KanSequence.mappingPre j (KanSequence.signedLoopTail Y.toKanSequence))
    (mappingPre_level_horn_rlp j (KanSequence.signedLoopTail Y.toKanSequence))
    (homOfParameterFamily X (KanSequence.signedLoopTail Y.toKanSequence) B
      (kanAdjointTracedBoundary X Y φ j))
    (fun n ↦ (kanAdjointTracedBoundaryCoordinate X Y φ j n).stage)
    (fun n ↦ (kanAdjointTracedBoundaryCoordinate X Y φ j n).projection)
    (kanAdjointCanonicalVerticalStructurePath X Y φ j) n

end SerrePositivity.KST.Spectra.RawSpectrumMapping
