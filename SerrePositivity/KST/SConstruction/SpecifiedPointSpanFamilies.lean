module
public import SerrePositivity.KST.SConstruction.SpecifiedPointSpanBoundary

/-! # 指定頂点の元の比較辺と外側三角形を全パラメータへ延長する
概要：元の一点の適合辺・実三角形を保持して、二円柱の全パラメータの実比較を作る。
方針：同じ指定境界を外側三角形の相対延長へ渡し、同じ選択の三面と境界を回収する。
規約：境界円柱を定数と仮定せず、元の適合辺と三角形をそのまま保持する。
使われ方：元の K prism の全精密化族を元の指定適合ホモトピーへ制限する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {U E : SSet.{u}} [KanComplex E] (u : U _⦋0⦌) {D : U ⟶ E}
  {x y : E _⦋0⦌} (a : SSet.Homotopy D (SSet.const x))
  (b : SSet.Homotopy D (SSet.const y)) (e : E.Edge x y) (t : E _⦋2⦌)
  (h₂ : E.map (SimplexCategory.δ (2 : Fin 3)).op t =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge a u).edge)
  (h₀ : E.map (SimplexCategory.δ (0 : Fin 3)).op t = e.edge)
  (h₁ : E.map (SimplexCategory.δ (1 : Fin 3)).op t =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge b u).edge)

/-- 指定頂点で元の比較辺を保持する、全パラメータの実比較円柱。 -/
def specifiedPointSpanComposite : SSet.Homotopy (SSet.const (X := U) x) (SSet.const y) :=
  relativeKanOuterSpanComposite (SSet.yonedaEquiv.symm u) a b (specifiedPointSpanEdge u e)
    (specifiedPointSpanTriangle u a b e t h₂ h₀ h₁)

/-- 比較円柱の指定頂点への制限は、元の指定比較辺の同じ実区間そのもの。 -/
lemma specifiedPointSpanComposite_boundary :
    (SSet.yonedaEquiv.symm u ▷ (Δ[1] : SSet.{u})) ≫
      (specifiedPointSpanComposite u a b e t h₂ h₀ h₁).h =
        snd (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ SSet.yonedaEquiv.symm e.edge := by
  rw [specifiedPointSpanComposite, relativeKanOuterSpanComposite_boundary]
  exact specifiedPointSimplex_uncurry e.edge

/-- 同じ選択から得る、二つの元の円柱と指定境界三角形を保持する全三角形族。 -/
def specifiedPointSpanTriangleFamily : U ⊗ (Δ[2] : SSet.{u}) ⟶ E :=
  relativeKanOuterSpanTriangleFamily (SSet.yonedaEquiv.symm u) a b (specifiedPointSpanEdge u e)
    (specifiedPointSpanTriangle u a b e t h₂ h₀ h₁)

/-- 全三角形族は指定頂点で元の外側三角形全体を厳密に回収する。 -/
lemma specifiedPointSpanTriangleFamily_boundary :
    (SSet.yonedaEquiv.symm u ▷ (Δ[2] : SSet.{u})) ≫
      specifiedPointSpanTriangleFamily u a b e t h₂ h₀ h₁ =
        snd (Δ[0] : SSet.{u}) (Δ[2] : SSet.{u}) ≫ SSet.yonedaEquiv.symm t := by
  rw [specifiedPointSpanTriangleFamily, relativeKanOuterSpanTriangleFamily_boundary]
  exact specifiedPointSimplex_uncurry t

/-- 全三角形族の第一面は、元の全パラメータの第一円柱そのもの。 -/
lemma specifiedPointSpanTriangleFamily_source :
    (U ◁ stdSimplex.δ 2) ≫ specifiedPointSpanTriangleFamily u a b e t h₂ h₀ h₁ = a.h :=
  relativeKanOuterSpanTriangleFamily_source _ _ _ _ _

/-- 全三角形族の第二面は、元の全パラメータの第二円柱そのもの。 -/
lemma specifiedPointSpanTriangleFamily_target :
    (U ◁ stdSimplex.δ 1) ≫ specifiedPointSpanTriangleFamily u a b e t h₂ h₀ h₁ = b.h :=
  relativeKanOuterSpanTriangleFamily_target _ _ _ _ _

/-- 全三角形族の残りの面は、同じ選択から得る比較円柱そのもの。 -/
lemma specifiedPointSpanTriangleFamily_composite :
    (U ◁ stdSimplex.δ 0) ≫ specifiedPointSpanTriangleFamily u a b e t h₂ h₀ h₁ =
      (specifiedPointSpanComposite u a b e t h₂ h₀ h₁).h :=
  relativeKanOuterSpanTriangleFamily_composite _ _ _ _ _

end SerrePositivity.KST.SConstruction
