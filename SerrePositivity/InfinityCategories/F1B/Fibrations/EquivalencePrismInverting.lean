module

public import SerrePositivity.InfinityCategories.Core.FunctorEdgePointwise
public import SerrePositivity.InfinityCategories.Core.PrecompositionEquivalence

/-!
概要：前合成同値への制限による prism の垂直辺の可逆性の検出。
方針：関手単体集合の指定辺を充満忠実な制限で反映し、各頂点で評価する。
規約：両端を結ぶ別の同型で代用せず、元の prism の辺を扱う。
使われ方：相対 Kan 拡張の可逆 path の延長。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：前合成同値への制限で可逆な prism は全頂点で可逆。
方針：curry した関手の辺の可逆性を反映し、評価によって元の垂直辺へ戻す。
規約：始域に充填性や頂点の全射性を要求しない。
使われ方：両端固定で延長した prism を可逆 path へ持ち上げる。 -/
lemma prism_pointwiseInvertible_of_restriction
    {A B X : SSet.{u}} [Quasicategory X] (i : A ⟶ B)
    (hi : IsPrecompositionEquivalence i) (H : (Δ[1] : SSet.{u}) ⊗ B ⟶ X)
    (hH : ∀ a : A _⦋0⦌, IsEquivalencePathVertex
      ((curry ((Δ[1] ◁ i) ≫ H)).app (Opposite.op ⦋0⦌) a)) :
    ∀ b : B _⦋0⦌, IsEquivalencePathVertex ((curry H).app (Opposite.op ⦋0⦌) b) := by
  let T : SSet.Homotopy (prismEndpoint 0 B ≫ H) (prismEndpoint 1 B ≫ H) :=
    { h := (β_ B (Δ[1] : SSet.{u})).hom ≫ H
      h₀ := by change prismEndpoint 0 B ≫ H = _; rfl
      h₁ := by change prismEndpoint 1 B ≫ H = _; rfl
      rel := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro s
        exact False.elim s.1.property }
  let q := (pre i).app X
  let e := functorEdgeOfSimplicialHomotopy T
  have he : IsInvertibleEdge (X := (ihom A).obj X) (e.map ((truncation 2).map q)) := by
    apply (isInvertibleEdge_iff_evaluateFunctorAt (K := A) (X := X)
      (f := i ≫ prismEndpoint 0 B ≫ H) (g := i ≫ prismEndpoint 1 B ≫ H)
      (e.map ((truncation 2).map q))).2
    intro a
    have ha := hH a
    unfold IsEquivalencePathVertex at ha
    rw [intervalFunctorVertexEdge_curry] at ha
    apply (isInvertibleEdge_congr (show
      (((e.map ((truncation 2).map q)).map
        ((truncation 2).map (evaluateFunctorAt (Y := X) a))).edge) =
        (edgeOfSimplex (((Δ[1] ◁ i) ≫ H).app (Opposite.op ⦋1⦌)
          (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant a 1))).edge from
      rfl)).mpr ha
  have he' := (hi X).isFullyFaithful.reflects_isInvertibleEdge e he
  intro b
  have hb := he'.map (evaluateFunctorAt (Y := X) b)
  unfold IsEquivalencePathVertex
  rw [intervalFunctorVertexEdge_curry]
  exact (isInvertibleEdge_congr (show
    ((e.map ((truncation 2).map (evaluateFunctorAt (Y := X) b))).edge) =
      (edgeOfSimplex (H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant b 1))).edge from
    rfl)).mp hb

end SerrePositivity.InfinityCategories.F1B
