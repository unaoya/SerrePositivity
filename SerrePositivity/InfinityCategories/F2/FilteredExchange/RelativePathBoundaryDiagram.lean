module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativePathBoundary
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.IntervalBoundaryPostcomposition

/-!
概要：元の二入力と指定部分 path から、相対 path 境界上の厳密な図式を作る。
方針：二端点の境界図式と指定部分 path を積の和の押し出しで貼る。
規約：全二端点と部分 path を選び直さない。
使われ方：全境界を固定する有限 Kan path 近似の anchor。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {K X : SSet.{u}} (A : K.Subcomplex) (f g : K ⟶ X)
  (a : (Δ[1] : SSet.{u}) ⊗ (A : SSet.{u}) ⟶ X)
  (h₀ : prismEndpoint 0 (A : SSet.{u}) ≫ a = A.ι ≫ f)
  (h₁ : prismEndpoint 1 (A : SSet.{u}) ≫ a = A.ι ≫ g)

/-- 概要：指定部分 path と全二端点を、相対境界上で貼り合わせる。
方針：積の和の押し出しと区間境界の制限式を使う。
規約：元の全境界図式。使われ方：相対有限近似の指定 anchor。 -/
def relativePathBoundaryDiagram : relativePathBoundaryShape A ⟶ X :=
  (Subcomplex.unionProd.isPushout (boundary 1) A).desc a (intervalBoundaryDiagram f g) (by
    rw [intervalBoundaryDiagram_restrict, h₀, h₁, intervalBoundaryDiagram_naturality])

/-- 概要：貼り合わせの部分 path 制限は元の指定 path。
方針：押し出しの第一脚。規約：全 path。使われ方：相対比較の側辺。 -/
lemma relativePathBoundaryDiagram_side :
    relativePathBoundarySide A ≫ relativePathBoundaryDiagram A f g a h₀ h₁ = a :=
  (Subcomplex.unionProd.isPushout (boundary 1) A).inl_desc _ _ _

/-- 概要：貼り合わせの両端制限は元の二入力の境界図式。
方針：押し出しの第二脚。規約：全二端点。使われ方：相対比較の入力。 -/
lemma relativePathBoundaryDiagram_ends :
    relativePathBoundaryEnds A ≫ relativePathBoundaryDiagram A f g a h₀ h₁ =
      intervalBoundaryDiagram f g :=
  (Subcomplex.unionProd.isPushout (boundary 1) A).inr_desc _ _ _

/-- 概要：貼り合わせの始点は元の第一入力。
方針：区間境界の始点を評価する。規約：厳密な式。使われ方：有限模型の第一端点。 -/
lemma relativePathBoundaryDiagram_zero :
    relativePathBoundaryEndpoint A 0 ≫ relativePathBoundaryDiagram A f g a h₀ h₁ = f := by
  rw [relativePathBoundaryEndpoint, Category.assoc, relativePathBoundaryDiagram_ends,
    intervalBoundaryDiagram_zero]

/-- 概要：貼り合わせの終点は元の第二入力。
方針：区間境界の終点を評価する。規約：厳密な式。使われ方：有限模型の第二端点。 -/
lemma relativePathBoundaryDiagram_one :
    relativePathBoundaryEndpoint A 1 ≫ relativePathBoundaryDiagram A f g a h₀ h₁ = g := by
  rw [relativePathBoundaryEndpoint, Category.assoc, relativePathBoundaryDiagram_ends,
    intervalBoundaryDiagram_one]

end SerrePositivity.InfinityCategories.F2
