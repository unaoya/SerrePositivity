module

public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.Core.EquivalencePath
public import SerrePositivity.InfinityCategories.Core.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Core.FunctorLimits
public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.PrismContraction
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeCoconeAbsolute
public import SerrePositivity.InfinityCategories.Core.CatInfinity.CoconeValEquality
public import SerrePositivity.InfinityCategories.F1.Presentable.LocalEquivalences
public import SerrePositivity.InfinityCategories.HomotopyLimits.ArrowCoconePrism
public import SerrePositivity.InfinityCategories.HomotopyLimits.ColimitPrismLocalApex
public import SerrePositivity.InfinityCategories.HomotopyLimits.ColimitPrismTotalCocone
public import SerrePositivity.InfinityCategories.HomotopyLimits.FunctorColimitEvaluation
public import SerrePositivity.InfinityCategories.HomotopyLimits.PrismVertexEvaluation

/-!
概要：元の矢印圏内の任意の指定余極限余錐について、局所同値な辺集合の閉性を証明する。
方針：元の余錐の評価・prism・全 Hom の普遍性を、厳密な射と同型で照合する。
規約：F2 は読み取り専用。使われ方：HTT 5.5.4.5・5.5.4.11 の強飽和性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 両端評価が余極限なら、局所同値な図式の元の矢印圏の余錐の頂点辺も局所同値。 -/
lemma localEquivalences_arrowCocone_of_endpoints {K X : SSet.{u}} [Quasicategory X]
    (W : Set (X _⦋1⦌)) {r : K ⟶ (ihom (Δ[1] : SSet.{u})).obj X} (c : JoinCocone r)
    (h₀ : IsColimitCone (F1B.kanPostcomposeCocone
      (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0)) c))
    (h₁ : IsColimitCone (F1B.kanPostcomposeCocone
      (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1)) c))
    (h : ∀ k : K _⦋0⦌, arrowVertexEdge (r.app (Opposite.op ⦋0⦌) k) ∈ localEquivalences W) :
    arrowVertexEdge c.vertex ∈ localEquivalences W := by
  rw [arrowCocone_vertex_prismEdge]
  apply localEquivalences_colimitPrism_apex W (uncurry c.val)
  · exact (F2.isColimitCone_iff_of_cocone_val_eq _ _ (arrowCocone_endpoint_val c 0)).mpr h₀
  · exact (F2.isColimitCone_iff_of_cocone_val_eq _ _ (arrowCocone_endpoint_val c 1)).mpr h₁
  · intro k
    rw [arrowCocone_prism_diagram, ← uncurry_vertex_prismEvaluation]
    exact h k

/-- 指定形状の余極限の存在の下、局所同値な図式の元の任意の矢印圏の余極限も局所同値。 -/
lemma localEquivalences_arrowColimit {K X : SSet.{u}} [Quasicategory X]
    (W : Set (X _⦋1⦌)) (hX : ∀ p : K ⟶ X, HasColimit p)
    {r : K ⟶ (ihom (Δ[1] : SSet.{u})).obj X} (c : JoinCocone r) (hc : IsColimitCone c)
    (h : ∀ k : K _⦋0⦌, arrowVertexEdge (r.app (Opposite.op ⦋0⦌) k) ∈ localEquivalences W) :
    arrowVertexEdge c.vertex ∈ localEquivalences W := by
  apply localEquivalences_arrowCocone_of_endpoints W c
  · exact isColimitCone_functor_evaluation_of_pointwise_exists c hc
      (fun k ↦ hX (evaluateFunctorDiagram r k)) _
  · exact isColimitCone_functor_evaluation_of_pointwise_exists c hc
      (fun k ↦ hX (evaluateFunctorDiagram r k)) _
  · exact h

end SerrePositivity.InfinityCategories.HomotopyLimits
