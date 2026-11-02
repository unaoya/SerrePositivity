module

public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.TransportTriangleComparisonAlong
public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.TransportSquareConstantTopNaturality

/-!
概要：三本の共通区間族上で表示した元の合成比較は、元の始点同型に自然。
方針：表示変更の等式を消去し、選択済み constantTopIso の自然性へ戻す。
規約：二つの元の sourceIso を保持。使われ方：四面の中間始点比較の移動。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 共通三辺上の元の合成比較の始点自然性。 -/
lemma TransportTriangleDiagram.comparisonAlong_source_naturality
    {E B P : SSet.{u}} {p : E ⟶ B} [LeftFibration p] {a b d : B _⦋0⦌}
    {s : TransportIntervalSquare P a b d d} {f : P ⟶ vertexFiber p a}
    {g : P ⟶ vertexFiber p b} {h : P ⟶ vertexFiber p d}
    (T : TransportTriangleDiagram p s f g h)
    (c₀₁ : P ⟶ intervalMappingSpace a b) (c₁₂ : P ⟶ intervalMappingSpace b d)
    (c₀₂ : P ⟶ intervalMappingSpace a d)
    (h₀₁ : s.bottom = c₀₁) (h₁₂ : s.right = c₁₂) (h₀₂ : s.left = c₀₂)
    {q r : P ⟶ vertexFiber p a} (e : FunctorIso q r) :
    diagonalFiberTransport_sourceIso p (diagonalFiberTransport_sourceIso p e c₀₁) c₁₂ ≪≫
        T.comparisonAlong r c₀₁ c₁₂ c₀₂ h₀₁ h₁₂ h₀₂ =
      T.comparisonAlong q c₀₁ c₁₂ c₀₂ h₀₁ h₁₂ h₀₂ ≪≫
        diagonalFiberTransport_sourceIso p e c₀₂ := by
  subst c₀₁ c₁₂ c₀₂
  exact transportIntervalSquare_constantTopIso_source_naturality p s T.top_base_constant e

end SerrePositivity.InfinityCategories.F2
