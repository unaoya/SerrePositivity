module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniverseFunctorIso
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniverseKan

/-!
概要：同じ実ホモトピーと関手同型の宇宙持ち上げ。
方針：円柱の各単体を上げ、各頂点の同じ可逆辺を移送する。
規約：straightening を import せず、新規の葉で閉じる。
使われ方：Ind-S (4) の小模型から大きい標的への延長の回収。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

/-- 元と同じ円柱ホモトピーを各次数で持ち上げる。 -/
def liftSimplicialHomotopy {X Y : SSet.{u}} {f g : X ⟶ Y} (H : SSet.Homotopy f g) :
    SSet.Homotopy ((SSet.uliftFunctor.{v, u}).map f) ((SSet.uliftFunctor.{v, u}).map g) where
  h := {
    app d := ↾fun x => ULift.up (H.h.app d (x.1.down, ULift.up x.2.down))
    naturality d e α := by
      apply ConcreteCategory.hom_ext
      intro x
      exact congrArg (fun k : (X ⊗ (Δ[1] : SSet.{u})).obj d ⟶ Y.obj e =>
        ULift.up (k (x.1.down, ULift.up x.2.down))) (H.h.naturality α) }
  h₀ := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg ULift.up (ConcreteCategory.congr_hom (NatTrans.congr_app H.h₀ n) x.down)
  h₁ := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg ULift.up (ConcreteCategory.congr_hom (NatTrans.congr_app H.h₁ n) x.down)
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 各点での辺も同じ元の辺の持ち上げになる。 -/
lemma liftSimplicialHomotopy_vertexEdge {X Y : SSet.{u}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f g) (x : X _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (liftSimplicialHomotopy.{u, v} H) (ULift.up x)).toTruncated =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.up (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).toTruncated := by
  apply Truncated.Edge.ext
  rfl

/-- 同じ全自然同型を元の二つの関手の宇宙持ち上げへ移す。 -/
def functorIso_ulift {X Y : SSet.{u}} [Quasicategory Y] {f g : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((SSet.uliftFunctor.{v, u}).map f) ((SSet.uliftFunctor.{v, u}).map g) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy (liftSimplicialHomotopy e.simplicialHomotopy) (by
    rintro ⟨x⟩
    rw [liftSimplicialHomotopy_vertexEdge]
    exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.invertible_up
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.simplicialHomotopyOfFunctorEdge_vertex_isInvertible
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.edge e) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.edge_isInvertible e) x))

/-- 同じ実ホモトピー逆を持ち上げる。 -/
lemma IsSimplicialHomotopyEquivalence.ulift {X Y : SSet.{u}} {f : X ⟶ Y}
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence ((SSet.uliftFunctor.{v, u}).map f) := by
  obtain ⟨g, ⟨H⟩, ⟨K⟩⟩ := h
  refine ⟨(SSet.uliftFunctor.{v, u}).map g, ?_, ?_⟩
  · simpa only [Functor.map_comp, (SSet.uliftFunctor.{v, u}).map_id] using
      (Nonempty.intro (liftSimplicialHomotopy.{u, v} H))
  · simpa only [Functor.map_comp, (SSet.uliftFunctor.{v, u}).map_id] using
      (Nonempty.intro (liftSimplicialHomotopy.{u, v} K))

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
