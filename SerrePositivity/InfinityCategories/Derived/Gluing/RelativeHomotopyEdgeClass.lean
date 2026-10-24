module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IntervalUncurryHomotopy
/-! # 両端を全時間で固定する二変形の辺の類

概要：同じ両端を全時間で固定する二次元比較から、関手圏の二辺の類の一致を得る。
方針：比較を関手単体集合の正方形へ curry し、退化する二側辺を消去する。
規約：端点一致だけではなく、両端の全時間固定を要求する。
使われ方：明示 augmentation prism の相対正規化を指定係数対角辺へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
lemma dgGluingHomotopySquare_homMk_eq {K Z : SSet.{u}} {f g : K ⟶ Z}
    (l r : SSet.Homotopy f g) (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom K).obj Z)
    (h0 : ι₀ ≫ Q = curry l.h) (h1 : ι₁ ≫ Q = curry r.h)
    (hx : prismEndpoint 0 Δ[1] ≫ Q = SSet.const (functorVertex f))
    (hy : prismEndpoint 1 Δ[1] ≫ Q = SSet.const (functorVertex g)) :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy l) =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy r) := by
  have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) = homotopyIntervalEdge.edge := by
    apply SSet.stdSimplex.ext
    intro j
    fin_cases j <;> rfl
  apply homMk_eq_of_square (functorEdgeOfSimplicialHomotopy l)
    (functorEdgeOfSimplicialHomotopy r) Q
  · change Q.app (Opposite.op ⦋1⦌) (homotopyIntervalEdge.edge,
      (SSet.Truncated.Edge.id (X := (truncation 2).obj (Δ[1] : SSet.{u}))
        (stdSimplex.obj₀Equiv.symm 0)).edge) = _
    rw [← hi]
    exact congrArg SSet.yonedaEquiv h0
  · change Q.app (Opposite.op ⦋1⦌) (homotopyIntervalEdge.edge,
      (SSet.Truncated.Edge.id (X := (truncation 2).obj (Δ[1] : SSet.{u}))
        (stdSimplex.obj₀Equiv.symm 1)).edge) = _
    rw [← hi]
    exact congrArg SSet.yonedaEquiv h1
  · change Q.app (Opposite.op ⦋1⦌)
      ((SSet.Truncated.Edge.id (X := (truncation 2).obj (Δ[1] : SSet.{u}))
        (stdSimplex.obj₀Equiv.symm 0)).edge, homotopyIntervalEdge.edge) = _
    rw [← hi]
    change SSet.yonedaEquiv (prismEndpoint 0 Δ[1] ≫ Q) = _
    rw [hx]
    exact pinchedConstant_one (X := (ihom K).obj Z) (functorVertex f)
  · change Q.app (Opposite.op ⦋1⦌)
      ((SSet.Truncated.Edge.id (X := (truncation 2).obj (Δ[1] : SSet.{u}))
        (stdSimplex.obj₀Equiv.symm 1)).edge, homotopyIntervalEdge.edge) = _
    rw [← hi]
    change SSet.yonedaEquiv (prismEndpoint 1 Δ[1] ≫ Q) = _
    rw [hy]
    exact pinchedConstant_one (X := (ihom K).obj Z) (functorVertex g)
lemma dgGluingRelativeHomotopy_homMk_eq {K Z : SSet.{u}} {f g : K ⟶ Z}
    (l r : SSet.Homotopy f g) (H : SSet.Homotopy l.h r.h)
    (hx : ((ι₀ : K ⟶ _) ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      CartesianMonoidalCategory.fst K (Δ[1] : SSet.{u}) ≫ f)
    (hy : ((ι₁ : K ⟶ _) ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      CartesianMonoidalCategory.fst K (Δ[1] : SSet.{u}) ≫ g) :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy l) =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy r) := by
  let Q := curry ((α_ K (Δ[1] : SSet.{u}) Δ[1]).inv ≫ H.h)
  apply dgGluingHomotopySquare_homMk_eq l r Q
  · change ι₀ ≫ curry ((α_ K (Δ[1] : SSet.{u}) Δ[1]).inv ≫ H.h) = _
    rw [← curry_natural_left]
    apply congrArg curry
    have he : (K ◁ (ι₀ : (Δ[1] : SSet.{u}) ⟶ _)) ≫
        (α_ K (Δ[1] : SSet.{u}) Δ[1]).inv = ι₀ := rfl
    rw [← Category.assoc, he, H.h₀]
  · change ι₁ ≫ curry ((α_ K (Δ[1] : SSet.{u}) Δ[1]).inv ≫ H.h) = _
    rw [← curry_natural_left]
    apply congrArg curry
    have he : (K ◁ (ι₁ : (Δ[1] : SSet.{u}) ⟶ _)) ≫
        (α_ K (Δ[1] : SSet.{u}) Δ[1]).inv = ι₁ := rfl
    rw [← Category.assoc, he, H.h₁]
  · change prismEndpoint 0 Δ[1] ≫
        curry ((α_ K (Δ[1] : SSet.{u}) Δ[1]).inv ≫ H.h) = _
    rw [← curry_natural_left]
    apply uncurry_injective
    rw [uncurry_curry, uncurry_const_functorVertex]
    have he : (K ◁ prismEndpoint 0 (Δ[1] : SSet.{u})) ≫
        (α_ K (Δ[1] : SSet.{u}) Δ[1]).inv =
        (ι₀ : K ⟶ _) ▷ (Δ[1] : SSet.{u}) := rfl
    rw [← Category.assoc, he, hx]
  · change prismEndpoint 1 Δ[1] ≫
        curry ((α_ K (Δ[1] : SSet.{u}) Δ[1]).inv ≫ H.h) = _
    rw [← curry_natural_left]
    apply uncurry_injective
    rw [uncurry_curry, uncurry_const_functorVertex]
    have he : (K ◁ prismEndpoint 1 (Δ[1] : SSet.{u})) ≫
        (α_ K (Δ[1] : SSet.{u}) Δ[1]).inv =
        (ι₁ : K ⟶ _) ▷ (Δ[1] : SSet.{u}) := rfl
    rw [← Category.assoc, he, hy]
end SerrePositivity.InfinityCategories
