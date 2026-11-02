module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.TransportTrianglePasting
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.TransportTriangleBaseAccess

/-!
概要：実三角形の指定合成比較を、等しい元の三本の区間族上で表示する。
方針：底の区間族の等式だけを消去し、元の constantTopIso を保持する。
規約：比較の値を再選択しない。使われ方：四面体の共通六辺への型合わせ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B P : SSet.{u}} {p : E ⟶ B} [LeftFibration p] {a b d : B _⦋0⦌}
  {s : TransportIntervalSquare P a b d d} {f : P ⟶ vertexFiber p a}
  {g : P ⟶ vertexFiber p b} {h : P ⟶ vertexFiber p d}
  (T : TransportTriangleDiagram p s f g h)

/-- 同じ三本の底の族を指定した、元の合成比較の表示。 -/
def TransportTriangleDiagram.comparisonAlong (q : P ⟶ vertexFiber p a)
    (c₀₁ : P ⟶ intervalMappingSpace a b) (c₁₂ : P ⟶ intervalMappingSpace b d)
    (c₀₂ : P ⟶ intervalMappingSpace a d)
    (h₀₁ : s.bottom = c₀₁) (h₁₂ : s.right = c₁₂) (h₀₂ : s.left = c₀₂) :
    FunctorIso (diagonalFiberTransport p (diagonalFiberTransport p q c₀₁) c₁₂)
      (diagonalFiberTransport p q c₀₂) := by
  subst c₀₁ c₁₂ c₀₂
  exact s.constantTopIso p q T.top_base_constant

/-- 底の三本の表示変更は、元の選択済み合成比較の値を保持する。 -/
lemma TransportTriangleDiagram.comparisonAlong_heq (q : P ⟶ vertexFiber p a)
    (c₀₁ : P ⟶ intervalMappingSpace a b) (c₁₂ : P ⟶ intervalMappingSpace b d)
    (c₀₂ : P ⟶ intervalMappingSpace a d)
    (h₀₁ : s.bottom = c₀₁) (h₁₂ : s.right = c₁₂) (h₀₂ : s.left = c₀₂) :
    HEq (T.comparisonAlong q c₀₁ c₁₂ c₀₂ h₀₁ h₁₂ h₀₂)
      (s.constantTopIso p q T.top_base_constant) := by
  subst c₀₁ c₁₂ c₀₂
  rfl

/-- 共通の三辺に表示を揃えても、実三辺の元の指定比較による貼り合わせ式を保つ。 -/
lemma TransportTriangleDiagram.comparisonAlong_eq
    (c₀₁ : P ⟶ intervalMappingSpace a b) (c₁₂ : P ⟶ intervalMappingSpace b d)
    (c₀₂ : P ⟶ intervalMappingSpace a d)
    (h₀₁ : s.bottom = c₀₁) (h₁₂ : s.right = c₁₂) (h₀₂ : s.left = c₀₂)
    (e₀₁ : FunctorIso g (diagonalFiberTransport p f c₀₁))
    (e₁₂ : FunctorIso h (diagonalFiberTransport p g c₁₂))
    (e₀₂ : FunctorIso h (diagonalFiberTransport p f c₀₂))
    (he₀₁ : HEq T.diagram.bottomComparison e₀₁)
    (he₁₂ : HEq T.diagram.rightComparison e₁₂)
    (he₀₂ : HEq T.diagram.leftComparison e₀₂) :
    T.comparisonAlong f c₀₁ c₁₂ c₀₂ h₀₁ h₁₂ h₀₂ =
      (e₁₂ ≪≫ diagonalFiberTransport_sourceIso p e₀₁ c₁₂).symm ≪≫ e₀₂ := by
  subst c₀₁ c₁₂ c₀₂
  cases eq_of_heq he₀₁
  cases eq_of_heq he₁₂
  cases eq_of_heq he₀₂
  exact T.constantTopIso_eq T.top_base_constant

end SerrePositivity.InfinityCategories.F2
