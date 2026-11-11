module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.SquareBoundary
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.ThreeEdgeSquarePath
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorDiagramPathUniqueness

/-!
概要：三角形の境界輸送から補完した正方形と元の正方形を全境界固定で比較する。
方針：三角形の path を畳み込みで正方形へ移し、始点と全境界 path を照合する。
規約：二辺は固定、対角の path は全体比較の右辺そのものと一致することを使う。
使われ方：B1 の順方向比較から復元した comma 正方形と元の図式を結ぶ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 概要：同じ境界 path を持つ三角形輸送の正方形補完と元の正方形は境界固定で結べる。
方針：畳み込みで輸送を正方形に移し、三辺と右辺で全境界 path の一致を証明する。
規約：輸送の path の終点だけでなく、指定した対角 path 全体の一致を要求する。
使われ方：B1 の復元した正方形から元の正方形への相対ホモトピー。 -/
lemma ThreeEdgeSquareComparison.exists_homotopy_to_triangleTransport
    {A X : SSet.{u}} [Quasicategory X] {U V W : A ⟶ X}
    {l : SSet.Homotopy U V} {r : SSet.Homotopy V W}
    {d₀ d₁ : SSet.Homotopy U W} {T : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d₀}
    {Q : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionSquare l r d₁} (c : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.ThreeEdgeSquareComparison T Q)
    (E : (Δ[2] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath ((ihom A).obj X))
    (hstart : E ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 0 = T.diagram)
    (h₀ : stdSimplex.δ (0 : Fin 3) ≫ E =
      stdSimplex.δ (0 : Fin 3) ≫ T.diagram ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl _)
    (h₂ : stdSimplex.δ (2 : Fin 3) ≫ E =
      stdSimplex.δ (2 : Fin 3) ≫ T.diagram ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl _)
    (h₁ : stdSimplex.δ (1 : Fin 3) ≫ E = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ c.path) :
    ∃ H : SSet.Homotopy Q.diagram (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareUpperFold ≫ E ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 1),
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareBoundary.ι ▷ (Δ[1] : SSet.{u})) ≫ H.h =
        fst _ (Δ[1] : SSet.{u}) ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareBoundary.ι ≫ Q.diagram := by
  let L := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareUpperFold ≫ E
  have h₃ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareThreeEdges.ι ≫ L =
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareThreeEdges.ι ≫ Q.diagram ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl _ := by
    apply _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareThreeEdges_restriction_eq L (Q.diagram ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl _)
    · change SSet.ι₀ ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareUpperFold ≫ E = SSet.ι₀ ≫ Q.diagram ≫ _
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareUpperFold_bottom]
      simp only [Category.assoc, h₂, reassoc_of% T.vertex_zero, reassoc_of% Q.bottom]
      rw [← Category.assoc, SSet.comp_const]
    · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareUpperFold ≫ E = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[1] ≫ Q.diagram ≫ _
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareUpperFold_left, h₂]
      rw [reassoc_of% T.face_two, reassoc_of% Q.left]
    · change SSet.ι₁ ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareUpperFold ≫ E = SSet.ι₁ ≫ Q.diagram ≫ _
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareUpperFold_top, h₀]
      rw [reassoc_of% T.face_zero, reassoc_of% Q.top]
  have hb : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareBoundary.ι ≫ c.path = _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareBoundary.ι ≫ L := by
    apply _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareBoundary_restriction_eq
    · exact c.path_restriction.trans (by simpa only [Category.assoc] using h₃.symm)
    · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[1] ≫ c.path = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareUpperFold ≫ E
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareUpperFold_right]
      exact h₁.symm
  have hs : c.path ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 0 = L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 0 := by
    rw [c.path_zero]
    change (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorSquareOfCompositionTriangle T).diagram = (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareUpperFold ≫ E) ≫ _
    rw [Category.assoc, hstart, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorSquareOfCompositionTriangle_eq_fold]
  obtain ⟨H, hH⟩ := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.exists_functorDiagramPath_endpointHomotopy _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareBoundary.ι c.path L hb hs
  let H' : SSet.Homotopy Q.diagram (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareUpperFold ≫ E ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 1) :=
    { h := H.h
      h₀ := H.h₀.trans c.path_one
      h₁ := H.h₁
      rel := H.rel }
  refine ⟨H', ?_⟩
  have hend : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareBoundary.ι ≫ L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 1 =
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareBoundary.ι ≫ Q.diagram := by
    have h := congrArg (fun k ↦ k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 1) hb.symm
    simpa only [Category.assoc, c.path_one] using h
  change (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareBoundary.ι ▷ (Δ[1] : SSet.{u})) ≫ H.h = _
  rw [hH, hend]

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
