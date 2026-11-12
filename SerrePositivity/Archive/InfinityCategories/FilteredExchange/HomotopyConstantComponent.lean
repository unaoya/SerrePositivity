module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.DegenerateEdgeIso
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorIsoPointEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Paths

/-!
概要：指定ホモトピーの同じ点での実辺が退化なら、その指定成分の同型は恒等。
方針：一点評価で元の辺の類を写し、退化辺の同型の値の計算へ戻す。
規約：元のホモトピーと実辺を保持。使われ方：定値係数での二側比較の計算。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 対象の元の等式に沿う恒等同型の値も、同じ恒等の値を保持する。 -/
lemma iso_refl_heq_of_eq {C : Type u} [Category.{v} C] {a b : C} (h : a = b) :
    HEq (Iso.refl a) (Iso.refl b) := by
  subst b
  rfl

/-- 同じ点での実円柱が定値なら、元の一点評価の実辺は同じ点の退化。 -/
lemma homotopyEvaluatedEdge_degenerate_of_constant {X Y : SSet.{u}}
    {f g : X ⟶ Y} (H : SSet.Homotopy f g) (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (h : lift (SSet.const x) (𝟙 (Δ[1] : SSet.{u})) ≫ H.h = SSet.const y) :
    ((functorEdgeOfSimplicialHomotopy H).map
      ((truncation 2).map (evaluateFunctorAt x))).edge = Y.σ 0 y := by
  have h' := congrArg (fun m : (Δ[1] : SSet.{u}) ⟶ Y =>
    m.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})))) h
  change H.h.app (Opposite.op ⦋1⦌)
    (PinchedHom.constant x 1, SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))) =
      PinchedHom.constant y 1 at h'
  change H.h.app (Opposite.op ⦋1⦌)
    (PinchedHom.constant x 1, SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))) = Y.σ 0 y
  simpa only [PinchedHom.constant_one] using h'

/-- 元の指定ホモトピーの一点評価の辺が退化なら、同じ指定成分は恒等の値。 -/
lemma homotopyIso_app_heq_refl_of_degenerate {X Y : SSet.{u}}
    [Quasicategory X] [KanComplex Y] {f g : X ⟶ Y} (H : SSet.Homotopy f g)
    (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (h : ((functorEdgeOfSimplicialHomotopy H).map
      ((truncation 2).map (evaluateFunctorAt x))).edge = Y.σ 0 y) :
    HEq ((functorIsoOfSimplicialHomotopy H).app x)
      (Iso.refl (SSet.HomotopyCategory.mk (g.app (Opposite.op ⦋0⦌) x))) := by
  let c := VertexIso.map (functorIsoOfSimplicialHomotopy H) (evaluateFunctorAt x)
  let e := SSet.Edge.ofTruncated (X := Y) ((functorEdgeOfSimplicialHomotopy H).map
    ((truncation 2).map (evaluateFunctorAt x)))
  have hc : c.hom = SSet.Truncated.HomotopyCategory.homMk e.toTruncated := rfl
  have he := vertexIso_heq_refl_of_degenerate_edge c e hc y h
  exact (functorIso_app_heq_evaluate (functorIsoOfSimplicialHomotopy H) x).trans
    (he.trans (iso_refl_heq_of_eq (congrArg SSet.HomotopyCategory.mk
      (evaluateFunctorAt_functorVertex x g))))

end SerrePositivity.InfinityCategories.F2
