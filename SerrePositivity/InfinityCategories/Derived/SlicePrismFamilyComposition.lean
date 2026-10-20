module
public import SerrePositivity.InfinityCategories.Derived.FunctorRightConstantSquare
public import SerrePositivity.InfinityCategories.Derived.PrismFunctorSquare

/-!
概要：実 slice の prism を全パラメータ関手圏の合成関係に移す。
方針：二重 prism の四辺を curry し、右辺が恒等の正方形を使う。
規約：標的の充填性・パラメータの有限性を仮定しない。使われ方：実屋根の合成評価。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
/-- 同じ三辺と全射影を持つ slice prism は、h Fun の指定三射の合成関係を与える。 -/
lemma slicePrismFamily_comp {K X : SSet.{u}} {U V : K ⟶ X} (z : X _⦋0⦌)
    (l : SSet.Homotopy U V) (r : SSet.Homotopy U (SSet.const z))
    (t : SSet.Homotopy V (SSet.const z))
    (P : (Δ[1] : SSet.{u}) ⊗ K ⟶ sliceOver (SSet.yonedaEquiv.symm z))
    (hb : (β_ K (Δ[1] : SSet.{u})).hom ≫ rightMappingSpacePrism K ≫
      sliceOverUncurry (prismEndpoint 0 K ≫ P) = r.h)
    (ht : (β_ K (Δ[1] : SSet.{u})).hom ≫ rightMappingSpacePrism K ≫
      sliceOverUncurry (prismEndpoint 1 K ≫ P) = t.h)
    (hl : (β_ K (Δ[1] : SSet.{u})).hom ≫ P ≫ sliceOverProjection _ = l.h) :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy l) ≫
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy t) =
        SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy r) := by
  apply functorHom_comp_eq_of_rightConstantSquare l r t
    (prismFunctorSquare (slicePrismSquare z P))
  · have h := prismFunctorSquare_inner (slicePrismSquare z P) 0
    simp only [↓reduceIte] at h
    rw [h, slicePrismSquare_inner, hb]
  · have h := prismFunctorSquare_inner (slicePrismSquare z P) 1
    simp only [Fin.one_eq_zero_iff, Nat.reduceEqDiff, ↓reduceIte] at h
    rw [h, slicePrismSquare_inner, ht]
  · rw [prismFunctorSquare_outer, slicePrismSquare_zero, hl]
  · rw [prismFunctorSquare_outer, slicePrismSquare_one, SSet.comp_const]
    apply uncurry_injective
    rw [uncurry_curry, uncurry_const_functorVertex, SSet.comp_const]
end SerrePositivity.InfinityCategories
