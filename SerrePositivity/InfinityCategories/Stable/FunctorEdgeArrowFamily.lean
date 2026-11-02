module
public import SerrePositivity.InfinityCategories.Core.FiniteShapes
public import SerrePositivity.InfinityCategories.Core.FunctorHomotopy
public import SerrePositivity.InfinityCategories.F2.Compact.FlipEvaluation

/-!
概要：全パラメーターに整合する実錐比較を、矢印圏の四角形へ移す。
方針：元の全単体・同じ比較辺・指定頂点への錐の移送を保持する。
規約：一般安定性を仮定しない。使われ方：HA 1.4.2.15 の第二条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

def arrowFamilyOfFunctorEdge {K X : SSet.{u}} {a b : ((ihom K).obj X) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj ((ihom K).obj X)) a b) :
    K ⟶ (ihom (Δ[1] : SSet.{u})).obj X :=
  internalHomFlipHomEquiv Δ[1] K X (SSet.yonedaEquiv.symm e.edge)

lemma arrowFamilyOfFunctorEdge_source {K X : SSet.{u}} {a b : ((ihom K).obj X) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj ((ihom K).obj X)) a b) :
    arrowFamilyOfFunctorEdge e ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) =
      (functorVertexEquiv K X).symm a := by
  apply functorVertex_injective
  have hs : functorVertex ((functorVertexEquiv K X).symm a) = a :=
    (functorVertexEquiv K X).apply_symm_apply a
  rw [hs, arrowFamilyOfFunctorEdge, F2.Compact.flipFamily_evaluate_vertex]
  have h := congrArg SSet.yonedaEquiv (edgeSimplex_source e)
  have hv : SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) :
      (Δ[0] : SSet.{u}) ⟶ Δ[1]) = stdSimplex.obj₀Equiv.symm (0 : Fin 2) := by decide
  simpa only [SSet.yonedaEquiv_comp, hv, Equiv.apply_symm_apply] using h

lemma arrowFamilyOfFunctorEdge_target {K X : SSet.{u}} {a b : ((ihom K).obj X) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj ((ihom K).obj X)) a b) :
    arrowFamilyOfFunctorEdge e ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1) =
      (functorVertexEquiv K X).symm b := by
  apply functorVertex_injective
  have hs : functorVertex ((functorVertexEquiv K X).symm b) = b :=
    (functorVertexEquiv K X).apply_symm_apply b
  rw [hs, arrowFamilyOfFunctorEdge, F2.Compact.flipFamily_evaluate_vertex]
  have h := congrArg SSet.yonedaEquiv (edgeSimplex_target e)
  have hv : SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) :
      (Δ[0] : SSet.{u}) ⟶ Δ[1]) = stdSimplex.obj₀Equiv.symm (1 : Fin 2) := by decide
  simpa only [SSet.yonedaEquiv_comp, hv, Equiv.apply_symm_apply] using h

lemma arrowFamilyOfFunctorEdge_vertex {K X : SSet.{u}} {a b : ((ihom K).obj X) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj ((ihom K).obj X)) a b) (k : K _⦋0⦌) :
    (arrowFamilyOfFunctorEdge e).app (Opposite.op ⦋0⦌) k =
      functorVertex (SSet.yonedaEquiv.symm e.edge ≫ evaluateFunctorAt k) :=
  internalHomFlipHomEquiv_app_zero _ _

end SerrePositivity.InfinityCategories
