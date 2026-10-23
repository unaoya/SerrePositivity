module

public import SerrePositivity.InfinityCategories.F2.Idempotent.IdemConeRetraction
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FilteredInfinity

/-!
概要：元の全 coherent 冪等図式の添字 Idem は、任意の κ について κ-filtered。
方針：恒等図式の実余錐を、任意の元の図式に沿って制限する。
規約：試験図式を nerve 上の図式へ制限せず、元の全単体を保持。
使われ方：Indκ の冪等完備性と、元の Yoneda retract 閉包からの実比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact

/-- 元の任意の全図式から Idem への写像は、同じ図式の実余錐を持つ。 -/
def idemShapeCocone {K : SSet.{u}} (f : K ⟶ Idempotent.IdemShape.{u}) : JoinCocone f :=
  ⟨joinMap f (𝟙 (Δ[0] : SSet.{u})) ≫ Idempotent.idemConeRetraction, by
    rw [← Category.assoc, joinInl_joinMap, Category.assoc,
      Idempotent.idemConeRetraction_inl, Category.comp_id]⟩

/-- 全 Idem は、κ-small な任意の coherent 試験図式について κ-filtered。 -/
lemma idemShape_isKappaFiltered (κ : Cardinal.{u}) :
    IsKappaFiltered κ Idempotent.IdemShape.{u} :=
  ⟨fun _ f ↦ ⟨idemShapeCocone f⟩⟩

end SerrePositivity.InfinityCategories.F2.Compact
