module

public import SerrePositivity.InfinityCategories.Core.EquivalencePathFinalLifting
public import SerrePositivity.InfinityCategories.Core.FullyFaithfulCalculus

/-!
概要：関手の同型による充満忠実性の不変性。
方針：可逆 path の二つの評価の充満忠実性で同じ射を検出する。
規約：関手単体集合のホモトピー圏の同型を使う。
使われ方：Kerodon Theorem 4.8.4.1 の path 置換への還元。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：可逆な垂直辺を持つホモトピーの両端で充満忠実性は同値。
方針：ホモトピーを可逆 path に持ち上げ、二つの評価で検出する。
規約：始域と標的は quasicategory。
使われ方：Kerodon §4.8.3–4.8.4 の関手の同値による不変性。 -/
lemma isFullyFaithful_iff_of_equivalenceHomotopy {A Y : SSet.{u}}
    [Quasicategory A] [Quasicategory Y]
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ Y)
    (hH : ∀ x : A _⦋0⦌, IsInvertibleEdge (edgeOfSimplex
      (H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1)))) :
    IsFullyFaithful (prismEndpoint 0 A ≫ H) ↔ IsFullyFaithful (prismEndpoint 1 A ≫ H) := by
  have hv : ∀ x, IsEquivalencePathVertex ((curry H).app (Opposite.op ⦋0⦌) x) := by
    intro x
    unfold IsEquivalencePathVertex
    rw [intervalFunctorVertexEdge_curry]
    exact hH x
  let a : A ⟶ equivalencePath Y := fullSubcomplexLift IsEquivalencePathVertex (curry H) hv
  have ha : a ≫ equivalencePathι Y = curry H := fullSubcomplexLift_ι _ _ _
  have he (i : Fin 2) : a ≫ equivalencePathEndpoint Y i = prismEndpoint i A ≫ H := by
    change a ≫ equivalencePathι Y ≫ evaluateFunctorAt _ = _
    rw [← Category.assoc, ha, curry_evaluateFunctorAt_interval]
  rw [← he 0, ← he 1]
  exact (isFullyFaithful_comp_iff a (equivalencePathEndpoint Y 0)
    (isFullyFaithful_of_trivialKanFibration _)).trans
      (isFullyFaithful_comp_iff a (equivalencePathEndpoint Y 1)
        (isFullyFaithful_of_trivialKanFibration _)).symm

/-- 概要：関手単体集合で同型な関手の充満忠実性は同値。
方針：同型を代表する辺を実際のホモトピーへ移す。
規約：両端の単体集合は quasicategory。
使われ方：Kerodon Theorem 4.8.4.1 の関手の置換。 -/
lemma FunctorIso.isFullyFaithful_iff {A Y : SSet.{u}}
    [Quasicategory A] [Quasicategory Y] {f g : A ⟶ Y} (e : FunctorIso f g) :
    IsFullyFaithful f ↔ IsFullyFaithful g := by
  let H := FunctorIso.simplicialHomotopy e
  let H' := (β_ (Δ[1] : SSet.{u}) A).hom ≫ H.h
  have h₀ : prismEndpoint 0 A ≫ H' = f := by
    rw [← Category.assoc, prismEndpoint_zero_braiding]
    exact H.h₀
  have h₁ : prismEndpoint 1 A ≫ H' = g := by
    rw [← Category.assoc, prismEndpoint_one_braiding]
    exact H.h₁
  have hv : ∀ x : A _⦋0⦌, IsInvertibleEdge (edgeOfSimplex
      (H'.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1))) := by
    intro x
    have he : H'.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1) =
        (simplicialHomotopyVertexEdge H x).edge := by
      change H.h.app (Opposite.op ⦋1⦌)
        (PinchedHom.constant x 1, SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))) =
        H.h.app (Opposite.op ⦋1⦌)
          ((SSet.Truncated.Edge.id (X := (truncation 2).obj A) x).edge, homotopyIntervalEdge.edge)
      have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) = homotopyIntervalEdge.edge := by
        apply stdSimplex.ext
        intro i
        fin_cases i <;> rfl
      rw [pinchedConstant_one, hi]
    exact (isInvertibleEdge_congr he).mpr
      (simplicialHomotopyOfFunctorEdge_vertex_isInvertible
        (FunctorIso.edge e) (FunctorIso.edge_isInvertible e) x)
  have h := isFullyFaithful_iff_of_equivalenceHomotopy H' hv
  rwa [h₀, h₁] at h

end SerrePositivity.InfinityCategories
