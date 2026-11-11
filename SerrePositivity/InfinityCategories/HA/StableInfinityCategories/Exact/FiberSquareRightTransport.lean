module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.FiberSquareComparison
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.SpecifiedFunctorEdgeLift
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SquareFunctorTransport
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.SimplexVertexDetection
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare

/-!
概要：fiber 四角形の右辺の指定関手同型を、全四角形の可逆辺へ厳密に持ち上げる。
方針：右辺包含の単射性と指定辺の相対持ち上げで、引き戻し性と零角を輸送する。
規約：右辺の元の一単体を保持。使われ方：d8 の中項を実積とする fiber 四角形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact
open _root_.SerrePositivity.KST.LocalizingInvariants

lemma fiberSquare_source_vertex {X : SSet.{u}} {x y : X _⦋0⦌}
    {f : Truncated.Edge (X := (truncation 2).obj X) x y} (s : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FiberSquare f) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex s.square 1 0 = x := by
  have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareRightEdge_source s.square
  rw [s.right_edge] at h
  exact h.symm.trans
    ((congrArg (X.δ 1) (SSet.yonedaEquiv.apply_symm_apply f.edge)).trans f.src_eq)

lemma fiberSquare_target_vertex {X : SSet.{u}} {x y : X _⦋0⦌}
    {f : Truncated.Edge (X := (truncation 2).obj X) x y} (s : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FiberSquare f) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex s.square 1 1 = y := by
  have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareRightEdge_target s.square
  rw [s.right_edge] at h
  exact h.symm.trans
    ((congrArg (X.δ 0) (SSet.yonedaEquiv.apply_symm_apply f.edge)).trans f.tgt_eq)

lemma exists_fiberSquare_right_transport {X : SSet.{u}} [Quasicategory X]
    (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsFiberSequence t) (g : (Δ[1] : SSet.{u}) ⟶ X)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ t.square)) :
    ∃ s : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FiberSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv g)),
      ∃ l : Truncated.Edge
        (X := (truncation 2).obj ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex s.square) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex t.square),
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge l ∧
          ((pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge).app X).app (Opposite.op ⦋1⦌) l.edge = e.edge.edge := by
  have : Mono _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge.{u} := by
    have h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge.{u} ≫ snd (Δ[1] : SSet.{u}) Δ[1] = 𝟙 Δ[1] := rfl
    exact mono_of_mono_fac h
  obtain ⟨G, hG, l, hl, hi⟩ := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.exists_precomposition_edge_lift
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge g t.square e.edge e.edge_isInvertible
  have : IsIso (SSet.Truncated.HomotopyCategory.homMk l) := hi
  let d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso G t.square := asIso (SSet.Truncated.HomotopyCategory.homMk l)
  have hz : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex G 0 1) := by
    let v : (Δ[1] ⊗ Δ[1] : SSet.{u}) _⦋0⦌ :=
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2))
    have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex G 0 1) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 0 1) := by
      have hv := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map d (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt v)
      simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex] at hv
      change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex G 0 1) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 0 1) at hv
      exact hv
    exact t.zero_corner.of_vertexIso he.symm
  let s : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FiberSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv g)) := {
    square := G
    zero_corner := hz
    right_edge := hG.trans (SSet.yonedaEquiv.symm_apply_apply g).symm
    isPullback := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsPullbackSquare.of_functorIso ht d.symm }
  exact ⟨s, l, hi, hl⟩

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exists_fiberSquare_right_transport := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.exists_fiberSquare_right_transport

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.fiberSquare_source_vertex := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.fiberSquare_source_vertex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.fiberSquare_target_vertex := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.fiberSquare_target_vertex
