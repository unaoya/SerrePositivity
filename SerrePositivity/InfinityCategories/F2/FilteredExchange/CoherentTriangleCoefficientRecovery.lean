module

public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCompositionTriangleRecovery

/-!
概要：元の coherent 合成四角形の全図式は、全係数の制限後も同じ三角形から戻る。
方針：折り畳みの係数自然性と元の全図式の回収を使う。
規約：元の二 Hom の族を保持。使われ方：一点係数を含む元の評価比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 三角形の折り畳みは元の全係数の制限を保つ。 -/
lemma transportTriangleParameter_naturality {P Q : SSet.{u}} (q : Q ⟶ P) :
    transportTriangleParameter Q ≫ (Δ[2] ◁ q) =
      (Δ[1] ◁ (Δ[1] ◁ q)) ≫ transportTriangleParameter P := by
  apply SSet.hom_ext
  intro n
  rfl

/-- 任意の同時係数制限でも、元の合成四角形全体を同じ三角形から回収する。 -/
lemma coherentCompositionSquare_triangle_recovery_precomp
    {C : Type v} [Category.{u} C] [SimplicialCategory C] (X Y Z : C)
    {P : SSet.{max u v}}
    (q : P ⟶ (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y) ⊗
      (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom Y Z)) :
    transportTriangleParameter P ≫ (Δ[2] ◁ q) ≫ coherentCompositionTriangle X Y Z =
      (Δ[1] ◁ (Δ[1] ◁ q)) ≫ coherentCompositionSquare X Y Z := by
  rw [← Category.assoc, transportTriangleParameter_naturality, Category.assoc,
    coherentCompositionSquare_triangle_recovery]

end SerrePositivity.InfinityCategories.F2
