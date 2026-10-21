module

public import SerrePositivity.InfinityCategories.Stable.CommutativeSquareRealization
public import SerrePositivity.InfinityCategories.Core.EquivalencePath

/-!
概要：元の四辺の Hom 可換式を、二つの指定辺の間の矢印関手圏の実際の辺へ移す。
方針：同じ四辺を保つ標準正方形を curry し、両端評価を厳密に回収する。
規約：四つの元の全一単体を変更せず、標的以外の充填性は要求しない。
使われ方：有限離散全錐の元の全脚の比較から、全錐の関手同型を構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
open SSet.Truncated.HomotopyCategory
variable {X : SSet.{u}} [Quasicategory X] {x y x' y' : X _⦋0⦌}
  (f : SSet.Edge x y) (g : SSet.Edge x' y') (a : SSet.Edge x x') (b : SSet.Edge y y')
  (h : homMk f.toTruncated ≫ homMk b.toTruncated =
    homMk a.toTruncated ≫ homMk g.toTruncated)

/-- 元の可換式の四辺をそのまま保持する、同じ一つの正方形。 -/
def commutingArrowSquare :
    {Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X //
      squareBottomEdge ≫ Q = SSet.yonedaEquiv.symm f.edge ∧
      squareTopEdge ≫ Q = SSet.yonedaEquiv.symm g.edge ∧
      squareLeftEdge ≫ Q = SSet.yonedaEquiv.symm a.edge ∧
      squareRightEdge ≫ Q = SSet.yonedaEquiv.symm b.edge} :=
  ⟨Classical.choose (exists_stableSquare_of_homMk_comm
      f.toTruncated g.toTruncated a.toTruncated b.toTruncated h),
    Classical.choose_spec (exists_stableSquare_of_homMk_comm
      f.toTruncated g.toTruncated a.toTruncated b.toTruncated h)⟩

/-- 同じ元の正方形を、指定した二辺の間の実際の円柱として表示する。 -/
def commutingArrowSquareHomotopy :
    SSet.Homotopy (SSet.yonedaEquiv.symm f.edge) (SSet.yonedaEquiv.symm g.edge) where
  h := (commutingArrowSquare f g a b h).val
  h₀ := by
    have he : (SSet.ι₀ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) = squareBottomEdge := by
      apply SSet.yonedaEquiv.injective
      apply Prod.ext <;> decide
    rw [he]
    exact (commutingArrowSquare f g a b h).property.1
  h₁ := by
    have he : (SSet.ι₁ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) = squareTopEdge := by
      apply SSet.yonedaEquiv.injective
      apply Prod.ext <;> decide
    rw [he]
    exact (commutingArrowSquare f g a b h).property.2.1
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property

/-- 同じ四辺を持つ正方形を、元の二辺の間の矢印関手圏の全辺として保持する。 -/
def commutingArrowSquareEdge :
    SSet.Edge (X := (ihom (Δ[1] : SSet.{u})).obj X)
      (functorVertex (SSet.yonedaEquiv.symm f.edge))
      (functorVertex (SSet.yonedaEquiv.symm g.edge)) :=
  SSet.Edge.ofTruncated (functorEdgeOfSimplicialHomotopy (commutingArrowSquareHomotopy f g a b h))

/-- 同じ矢印関手圏の辺の始点評価は、元の指定左辺の全一単体。 -/
lemma commutingArrowSquareEdge_zero :
    ((commutingArrowSquareEdge f g a b h).map
      (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))).edge = a.edge := by
  change SSet.yonedaEquiv (curry (commutingArrowSquare f g a b h).val ≫
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) = _
  rw [curry_evaluateFunctorAt_interval]
  have he : prismEndpoint 0 (Δ[1] : SSet.{u}) = squareLeftEdge := by
    apply SSet.yonedaEquiv.injective
    apply Prod.ext <;> decide
  rw [he, (commutingArrowSquare f g a b h).property.2.2.1, Equiv.apply_symm_apply]

/-- 同じ矢印関手圏の辺の終点評価は、元の指定右辺の全一単体。 -/
lemma commutingArrowSquareEdge_one :
    ((commutingArrowSquareEdge f g a b h).map
      (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))).edge = b.edge := by
  change SSet.yonedaEquiv (curry (commutingArrowSquare f g a b h).val ≫
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) = _
  rw [curry_evaluateFunctorAt_interval]
  have he : prismEndpoint 1 (Δ[1] : SSet.{u}) = squareRightEdge := by
    apply SSet.yonedaEquiv.injective
    apply Prod.ext <;> decide
  rw [he, (commutingArrowSquare f g a b h).property.2.2.2, Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories.HomotopyLimits
