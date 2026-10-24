module
public import SerrePositivity.InfinityCategories.Core.LimitConeExtension
public import SerrePositivity.InfinityCategories.Core.EquivalenceCylinderFunctorIso
/-!
概要：関手同型で結ばれた実図式の極限の存在を輸送する。
方針：可逆円柱へ延長し、両端の同値な単射に沿う実錐の制限を使う。
規約：添字には quasicategory 性を課さない。使われ方：反転された実分母図式の極限。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
/-- 同値な単射に沿う制限は、実極限の存在を保存し反映する。 -/
lemma hasLimit_iff_restrict_of_precompositionEquivalence {K L X : SSet.{u}}
    [Quasicategory X] (p : K ⟶ X) (f : L ⟶ K) [Mono f]
    (hf : IsPrecompositionEquivalence f) : HasLimit p ↔ HasLimit (f ≫ p) := by
  have := sliceOverRestrict_trivialKanFibration_of_precompositionEquivalence p f hf
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨restrictJoinCone c f, ?_⟩
    exact ((qCatEquivalenceOfTrivialKanFibration
      (sliceOverRestrict p f)).isTerminalVertex_iff c).mp hc
  · rintro ⟨d, hd⟩
    obtain ⟨c, hc, _, _⟩ := exists_limitCone_extension_of_trivialRestriction p f d hd
    exact ⟨c, hc⟩
/-- 可逆円柱の両端の実図式は、極限の存在が同値。 -/
lemma hasLimit_iff_equivalenceCylinder_endpoints {K X : SSet.{u}} [Quasicategory X]
    (H : K ⊗ equivalenceInterval ⟶ X) :
    HasLimit (equivalenceCylinderEndpoint K false ≫ H) ↔
      HasLimit (equivalenceCylinderEndpoint K true ≫ H) :=
  (hasLimit_iff_restrict_of_precompositionEquivalence H _
    (isPrecompositionEquivalence_equivalenceCylinderEndpoint K false)).symm.trans
      (hasLimit_iff_restrict_of_precompositionEquivalence H _
        (isPrecompositionEquivalence_equivalenceCylinderEndpoint K true))
/-- 同型な実図式は、任意 quasicategory 標的で極限の存在が同値。 -/
lemma hasLimit_iff_of_functorIso {K X : SSet.{u}} [Quasicategory X] {p q : K ⟶ X}
    (e : FunctorIso p q) : HasLimit p ↔ HasLimit q := by
  obtain ⟨H, h₀, h₁⟩ := exists_equivalenceCylinder_extension_of_functorIso e
  have h := hasLimit_iff_equivalenceCylinder_endpoints H
  rw [h₀, h₁] at h
  exact h
end SerrePositivity.InfinityCategories
