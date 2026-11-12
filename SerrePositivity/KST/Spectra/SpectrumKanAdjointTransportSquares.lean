module

public import SerrePositivity.KST.Spectra.ThreeEdgeTransportSquareProjection
public import SerrePositivity.KST.Spectra.SpectrumKanAdjointCanonicalStageTransport

/-!
概要：元の Kan 随伴の段調整の三辺輸送を、同じ四辺と非零境界を保持する正方形へ戻す。
方針：選択済みの二つの輸送三角形を貼り、その境界輸送への厳密射影を検査する。
規約：三角形も四辺も変更しない。使われ方：段調整と相対厳密化の正方形の貼り合わせ。
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

/-- 元の二つの輸送三角形から、同じ段調整区間の間の実正方形を構成する。 -/
def kanAdjointCanonicalTransportSquare (n : ℕ) :=
  (_root_.SerrePositivity.KST.Spectra.ThreeEdgeTransport.square (kanAdjointCanonicalStageTransport X Y φ j n))

/-- 保存した第一の二単体は、正方形の上側の同じ二単体。 -/
lemma kanAdjointCanonicalTransportSquare_upper (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper ≫ kanAdjointCanonicalTransportSquare X Y φ j n =
      SSet.yonedaEquiv.symm (kanAdjointCanonicalStageTransport X Y φ j n).first.simplex :=
  ThreeEdgeTransport.square_upper _

/-- 保存した第二の二単体も、正方形の下側の同じ二単体。 -/
lemma kanAdjointCanonicalTransportSquare_lower (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower ≫ kanAdjointCanonicalTransportSquare X Y φ j n =
      SSet.yonedaEquiv.symm (kanAdjointCanonicalStageTransport X Y φ j n).second.simplex :=
  ThreeEdgeTransport.square_lower _

/-- 左端の境界は、元の Kan 随伴構造区間そのもの。 -/
lemma kanAdjointCanonicalTransportSquare_start (n : ℕ) :
    stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u}) ≫
        kanAdjointCanonicalTransportSquare X Y φ j n =
      snd (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫
        (kanAdjointTracedStructureInterval X Y φ n).path := by
  rw [kanAdjointCanonicalTransportSquare, ThreeEdgeTransport.square_start]
  exact congrArg (_ ≫ ·) (Equiv.symm_apply_apply _ _)

/-- 右端の境界は、同じ輸送辺から戻した調整済み構造区間そのもの。 -/
lemma kanAdjointCanonicalTransportSquare_finish (n : ℕ) :
    stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u}) ≫
        kanAdjointCanonicalTransportSquare X Y φ j n =
      snd (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫
        (kanAdjointCanonicalStageStructurePath X Y φ j n).path :=
  ThreeEdgeTransport.square_finish _

/-- 正方形全体の非零境界への射影は、同じ二つの境界輸送三角形から作った正方形。 -/
lemma kanAdjointCanonicalTransportSquare_projection (n : ℕ) :
    kanAdjointCanonicalTransportSquare X Y φ j n ≫
      (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
        ((KanSequence.mappingPre j (KanSequence.signedLoopTail Y.toKanSequence)).app
          (n + 1))).right =
      (_root_.SerrePositivity.KST.Spectra.ThreeEdgeTransport.square (kanAdjointCanonicalBoundaryTransport X Y φ j n)) := by
  rw [kanAdjointCanonicalTransportSquare, ThreeEdgeTransport.square_map]
  exact ThreeEdgeTransport.square_eq_of_simplex_eq _ _ rfl rfl

end SerrePositivity.KST.Spectra.RawSpectrumMapping
