module
public import SerrePositivity.InfinityCategories.Stable.Quasicategory.ArrowFamilyRecoveredEdge

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

/-- 元の全辺族から、同じ固定両端点を持つパラメータ関手圏の実辺を回収する。 -/
def spanArrowFamilyEdge : SSet.Edge (functorVertex (SSet.const x : K ⟶ X))
    (functorVertex (SSet.const y : K ⟶ X)) :=
  intervalMappingFamilyEdge (spanArrowFamilyMapping f h₀ h₁)

lemma spanArrowFamilyEdge_edge : (spanArrowFamilyEdge f h₀ h₁).edge =
    SSet.yonedaEquiv (internalHomFlipHomEquiv K Δ[1] X f) := by
  rw [spanArrowFamilyEdge, intervalMappingFamilyEdge_edge, _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.spanArrowFamilyMapping_inclusion]

/-- 固定端点 Hom 内の比較は、元の二辺族から回収した同じ実辺の Hom 類を一致させる。 -/
lemma spanArrowFamilyEdge_homMk_eq [Quasicategory X]
    (g : K ⟶ (ihom (Δ[1] : SSet.{u})).obj X)
    (hg₀ : g ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = SSet.const x)
    (hg₁ : g ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = SSet.const y)
    (e : FunctorIso (spanArrowFamilyMapping f h₀ h₁) (spanArrowFamilyMapping g hg₀ hg₁)) :
    Truncated.HomotopyCategory.homMk (spanArrowFamilyEdge f h₀ h₁).toTruncated =
      Truncated.HomotopyCategory.homMk (spanArrowFamilyEdge g hg₀ hg₁).toTruncated :=
  intervalMappingFamilyEdge_homMk_eq e

end SerrePositivity.KST.LocalizingInvariants
