module

public import SerrePositivity.KST.LocalizingInvariants.IntervalMappingFamilyTranspose
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.MappingSpaceIntervalComparison

/-!
概要：両端点を固定した元の全辺族を、パラメータ関手圏の同じ実辺へ戻す。
方針：同じ uncurry を区間 Hom の厳密 fiber に入れ、全族の転置を適用する。
規約：回収辺の一次単体は元の全族の転置と厳密に一致する。
使われ方：元の分母・次辺・回収商辺を同じ Hom 内で合成し比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {K X : SSet.{u}} {x y : X _⦋0⦌}
  (f : K ⟶ (ihom (Δ[1] : SSet.{u})).obj X)
  (h₀ : f ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = SSet.const x)
  (h₁ : f ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = SSet.const y)

/-- 元の両端点を厳密に保持した、同じ全辺族の区間 Hom 表示。 -/
def spanArrowFamilyMapping : K ⟶ intervalMappingSpace x y :=
  intervalMappingCurryOfEndpoints (uncurry f)
    (by rw [← curry_evaluateFunctorAt_interval, curry_uncurry]; exact h₀)
    (by rw [← curry_evaluateFunctorAt_interval, curry_uncurry]; exact h₁)

/-- 区間 Hom 表示を包含しても、元の全辺族は変わらない。 -/
lemma spanArrowFamilyMapping_inclusion : spanArrowFamilyMapping f h₀ h₁ ≫
    vertexFiberι ((pre (boundary 1).ι).app X)
      (functorVertex (intervalMappingBoundary x y)) = f := by
  apply uncurry_injective
  change intervalMappingUncurry (spanArrowFamilyMapping f h₀ h₁) = _
  exact intervalMappingUncurry_curryOfEndpoints _ _ _

/-- 元の全辺族から、同じ固定両端点を持つパラメータ関手圏の実辺を回収する。 -/
def spanArrowFamilyEdge : SSet.Edge (functorVertex (SSet.const x : K ⟶ X))
    (functorVertex (SSet.const y : K ⟶ X)) :=
  intervalMappingFamilyEdge (spanArrowFamilyMapping f h₀ h₁)

lemma spanArrowFamilyEdge_edge : (spanArrowFamilyEdge f h₀ h₁).edge =
    SSet.yonedaEquiv (internalHomFlipHomEquiv K Δ[1] X f) := by
  rw [spanArrowFamilyEdge, intervalMappingFamilyEdge_edge, spanArrowFamilyMapping_inclusion]

/-- 固定端点 Hom 内の比較は、元の二辺族から回収した同じ実辺の Hom 類を一致させる。 -/
lemma spanArrowFamilyEdge_homMk_eq [Quasicategory X]
    (g : K ⟶ (ihom (Δ[1] : SSet.{u})).obj X)
    (hg₀ : g ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = SSet.const x)
    (hg₁ : g ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = SSet.const y)
    (e : FunctorIso (spanArrowFamilyMapping f h₀ h₁) (spanArrowFamilyMapping g hg₀ hg₁)) :
    Truncated.HomotopyCategory.homMk (spanArrowFamilyEdge f h₀ h₁).toTruncated =
      Truncated.HomotopyCategory.homMk (spanArrowFamilyEdge g hg₀ hg₁).toTruncated :=
  intervalMappingFamilyEdge_homMk_eq e

/-- 定値な実辺の族の始点は、元の同じ始点に厳密に定値。 -/
lemma spanConstantArrowFamily_source {Y P : SSet.{u}} {a b : Y _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj Y) a b) :
    (SSet.const (functorVertex (SSet.yonedaEquiv.symm e.edge)) :
      P ⟶ (ihom (Δ[1] : SSet.{u})).obj Y) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = SSet.const a := by
  rw [SSet.const_comp, evaluateFunctorAt_functorVertex]
  have hp : stdSimplex.obj₀Equiv.symm (0 : Fin 2) =
      SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) := by decide
  rw [hp, ← SSet.yonedaEquiv_comp, edgeSimplex_source, Equiv.apply_symm_apply]

lemma spanConstantArrowFamily_target {Y P : SSet.{u}} {a b : Y _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj Y) a b) :
    (SSet.const (functorVertex (SSet.yonedaEquiv.symm e.edge)) :
      P ⟶ (ihom (Δ[1] : SSet.{u})).obj Y) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = SSet.const b := by
  rw [SSet.const_comp, evaluateFunctorAt_functorVertex]
  have hp : stdSimplex.obj₀Equiv.symm (1 : Fin 2) =
      SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) := by decide
  rw [hp, ← SSet.yonedaEquiv_comp, edgeSimplex_target, Equiv.apply_symm_apply]

end SerrePositivity.KST.LocalizingInvariants
