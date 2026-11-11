module

public import SerrePositivity.KST.LocalizingInvariants.CompositionTriangleHomotopy
public import SerrePositivity.KST.LocalizingInvariants.TrianglePrismCommutation

/-!
概要：同じ二辺を固定した実相対 prism に、二つの全 h Fun 可換式を適用する。
方針：元の prism の固定面を使い、一般の三角形ホモトピーの自然性へ渡す。
規約：可換式は入力にしない。使われ方：Sp 二単体から標準合成三角形への比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.TriangleComparison

variable {X : SSet.{u}} [Quasicategory X] {x y z : X _⦋0⦌}
  (e : X.Edge x y) (f : X.Edge y z) (s t : X _⦋2⦌)
  (hs₂ : X.δ 2 s = e.edge) (hs₀ : X.δ 0 s = f.edge)
  (ht₂ : X.δ 2 t = e.edge) (ht₀ : X.δ 0 t = f.edge)

lemma homotopy_first :
    (TrianglePrism.firstFace (homotopy e f s t hs₂ hs₀ ht₂ ht₀)).h =
      fst (Δ[1] : SSet.{u}) Δ[1] ≫ SSet.yonedaEquiv.symm e.edge := by
  exact (congrArg (fun k ↦ (stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫ k)
    (homotopy_map e f s t hs₂ hs₀ ht₂ ht₀)).trans
      (prism_first e f s t hs₂ hs₀ ht₂ ht₀)

lemma homotopy_last :
    (TrianglePrism.lastFace (homotopy e f s t hs₂ hs₀ ht₂ ht₀)).h =
      fst (Δ[1] : SSet.{u}) Δ[1] ≫ SSet.yonedaEquiv.symm f.edge := by
  exact (congrArg (fun k ↦ (stdSimplex.δ (0 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫ k)
    (homotopy_map e f s t hs₂ hs₀ ht₂ ht₀)).trans
      (prism_last e f s t hs₂ hs₀ ht₂ ht₀)

lemma post_commutation :
    Arrow.mk (Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (TriangleEdge.post (SSet.yonedaEquiv.symm s))) ≫
        Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
          (TrianglePrism.diagonalFace (homotopy e f s t hs₂ hs₀ ht₂ ht₀)))) =
    Arrow.mk (Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (TriangleEdge.post (SSet.yonedaEquiv.symm t)))) :=
  TrianglePrism.post_commutation _ _ (homotopy_first e f s t hs₂ hs₀ ht₂ ht₀)

lemma pre_commutation :
    Arrow.mk (Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (TriangleEdge.pre (SSet.yonedaEquiv.symm s)))) =
    Arrow.mk (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (TrianglePrism.diagonalFace (homotopy e f s t hs₂ hs₀ ht₂ ht₀))) ≫
        Truncated.HomotopyCategory.homMk
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (TriangleEdge.pre (SSet.yonedaEquiv.symm t)))) :=
  TrianglePrism.pre_commutation _ _ (homotopy_last e f s t hs₂ hs₀ ht₂ ht₀)

end SerrePositivity.KST.LocalizingInvariants.TriangleComparison
