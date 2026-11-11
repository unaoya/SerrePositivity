module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitNativeIntervalPath
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.SquareClass

/-!
概要：元の余極限指定辺と a6 の native 区間表示が同じ射を表すことを証明する。
方針：元の比較円柱の四辺を計算し、両端固定の正方形の合成関係を適用する。
規約：始点の頂点等式だけを反映。使われ方：元の cospan の脚の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (H : SSet.Homotopy F G)

/-- 元の余極限指定辺を、元の余錐の始点頂点で読む。同じ一次単体を保持する。 -/
def coherentColimitAdjustedEdge : SSet.Truncated.Edge (X := (truncation 2).obj SpaceInfinity.{u})
    (coherentDiagramTotalCocone F).vertex (coherentDiagramTotalVertex G) :=
  ⟨(coherentColimitFunctorEdge B H).edge,
    (coherentColimitFunctorEdge B H).src_eq.trans (coherentDiagramTotalCocone_vertex F).symm,
    (coherentColimitFunctorEdge B H).tgt_eq⟩

/-- 元の余極限指定辺と選択済み native 辺の区間表示は、元の両端間の同じ射を表す。 -/
lemma coherentColimitEdge_homMk_eq_native :
    SSet.Truncated.HomotopyCategory.homMk (coherentColimitAdjustedEdge B H) =
      SSet.Truncated.HomotopyCategory.homMk
        (intervalMappingEdgeOfVertex (coherentColimitNativeIntervalVertex B H)).toTruncated := by
  let Q := coherentColimitIntervalNativeHomotopy B H
  have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u + 1})) = homotopyIntervalEdge.edge := by
    apply SSet.stdSimplex.ext
    intro j
    fin_cases j <;> rfl
  apply homMk_eq_of_square _ _ Q.h
  · change Q.h.app (Opposite.op ⦋1⦌) (homotopyIntervalEdge.edge, _) = _
    rw [← hi]
    change SSet.yonedaEquiv (SSet.ι₀ ≫ Q.h) = _
    rw [Q.h₀]
    exact Equiv.apply_symm_apply _ _
  · change Q.h.app (Opposite.op ⦋1⦌) (homotopyIntervalEdge.edge, _) = _
    rw [← hi]
    change SSet.yonedaEquiv (SSet.ι₁ ≫ Q.h) = _
    rw [Q.h₁]
    rfl
  · change Q.h.app (Opposite.op ⦋1⦌) (_, homotopyIntervalEdge.edge) = _
    rw [← hi]
    change SSet.yonedaEquiv (prismEndpoint 0 Δ[1] ≫ Q.h) = _
    rw [coherentColimitIntervalNativeHomotopy_source]
    exact pinchedConstant_one (X := SpaceInfinity.{u}) (coherentDiagramTotalCocone F).vertex
  · change Q.h.app (Opposite.op ⦋1⦌) (_, homotopyIntervalEdge.edge) = _
    rw [← hi]
    change SSet.yonedaEquiv (prismEndpoint 1 Δ[1] ≫ Q.h) = _
    rw [coherentColimitIntervalNativeHomotopy_target]
    exact pinchedConstant_one (X := SpaceInfinity.{u}) (coherentDiagramTotalVertex G)

end SerrePositivity.InfinityCategories.F2
