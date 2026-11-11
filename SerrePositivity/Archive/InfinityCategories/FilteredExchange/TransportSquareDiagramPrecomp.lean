module

public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.TransportSquareDiagramChosenComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IntervalSquareReindex

/-!
概要：任意の実四角形を、全係数と四隅の実値を保って制限する。
方針：二つの区間を固定し、四隅の端点自然性を二回適用する。
規約：元の実全四角形を保持。使われ方：同じ高次図式の実面の係数自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 係数を制限してから取った四隅は、元の同じ四隅の係数制限に一致する。 -/
lemma transportSquareCorner_precomp {P Q : SSet.{u}} (q : Q ⟶ P) (i j : Fin 2) :
    (prismEndpoint i Q ≫ prismEndpoint j (Δ[1] ⊗ Q)) ≫ (Δ[1] ◁ (Δ[1] ◁ q)) =
      q ≫ (prismEndpoint i P ≫ prismEndpoint j (Δ[1] ⊗ P)) := by
  rw [Category.assoc, prismEndpoint_naturality, ← Category.assoc,
    prismEndpoint_naturality, Category.assoc]

/-- 任意の実四角形の係数を制限し、同じ四つの実 fiber 値を保持する。 -/
def TransportSquareDiagram.precomp {E B P Q : SSet.{u}} {p : E ⟶ B}
    {a b c d : B _⦋0⦌} {s : TransportIntervalSquare P a b c d}
    {f : P ⟶ vertexFiber p a} (D : TransportSquareDiagram p s f) (q : Q ⟶ P) :
    TransportSquareDiagram p (s.precomp q) (q ≫ f) where
  bottomRight := q ≫ D.bottomRight
  topLeft := q ≫ D.topLeft
  topRight := q ≫ D.topRight
  square := (Δ[1] ◁ (Δ[1] ◁ q)) ≫ D.square
  over_base := by rw [Category.assoc, D.over_base]; rfl
  origin := by
    rw [← Category.assoc, transportSquareCorner_precomp, Category.assoc,
      D.origin, Category.assoc]
  bottomRight_eq := by
    rw [← Category.assoc, transportSquareCorner_precomp, Category.assoc,
      D.bottomRight_eq, Category.assoc]
  topLeft_eq := by
    rw [← Category.assoc, transportSquareCorner_precomp, Category.assoc,
      D.topLeft_eq, Category.assoc]
  topRight_eq := by
    rw [← Category.assoc, transportSquareCorner_precomp, Category.assoc,
      D.topRight_eq, Category.assoc]

end SerrePositivity.InfinityCategories.F2
