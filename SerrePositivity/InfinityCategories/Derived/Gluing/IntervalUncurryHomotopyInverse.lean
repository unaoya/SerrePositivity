module
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.MappingSpaceIntervalComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.IntervalUncurryHomotopyBoundary

/-! 両側辺を固定する同じ実円柱を、区間 Hom 族のホモトピーへ戻す。 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
variable {K X : SSet.{u}} {x y : X _⦋0⦌}
  {f g : K ⟶ intervalMappingSpace x y}
  (H : SSet.Homotopy (intervalMappingUncurry f) (intervalMappingUncurry g))
  (hx : (prismEndpoint 0 K ▷ (Δ[1] : SSet.{u})) ≫ H.h = SSet.const x)
  (hy : (prismEndpoint 1 K ▷ (Δ[1] : SSet.{u})) ≫ H.h = SSet.const y)

def dgGluingIntervalUncurryHomotopyInverseMap : K ⊗ (Δ[1] : SSet.{u}) ⟶
    intervalMappingSpace x y :=
  intervalMappingCurryOfEndpoints
    ((α_ (Δ[1] : SSet.{u}) K (Δ[1] : SSet.{u})).inv ≫ H.h) (by
      have hi : prismEndpoint 0 (K ⊗ (Δ[1] : SSet.{u})) ≫
          (α_ (Δ[1] : SSet.{u}) K (Δ[1] : SSet.{u})).inv =
        prismEndpoint 0 K ▷ (Δ[1] : SSet.{u}) := rfl
      rw [← Category.assoc, hi, hx]) (by
      have hi : prismEndpoint 1 (K ⊗ (Δ[1] : SSet.{u})) ≫
          (α_ (Δ[1] : SSet.{u}) K (Δ[1] : SSet.{u})).inv =
        prismEndpoint 1 K ▷ (Δ[1] : SSet.{u}) := rfl
      rw [← Category.assoc, hi, hy])

lemma dgGluingIntervalUncurryHomotopyInverseMap_evaluate :
    (α_ (Δ[1] : SSet.{u}) K (Δ[1] : SSet.{u})).hom ≫
        intervalMappingUncurry (dgGluingIntervalUncurryHomotopyInverseMap H hx hy) = H.h := by
  rw [dgGluingIntervalUncurryHomotopyInverseMap,
    intervalMappingUncurry_curryOfEndpoints, Iso.hom_inv_id_assoc]

def dgGluingIntervalUncurryHomotopyInverse : SSet.Homotopy f g where
  h := dgGluingIntervalUncurryHomotopyInverseMap H hx hy
  h₀ := by
    apply intervalMappingUncurry_injective x y
    rw [intervalMappingUncurry_precomp, dgGluingIntervalUncurryHomotopyInverseMap,
      intervalMappingUncurry_curryOfEndpoints]
    have hi : ((Δ[1] : SSet.{u}) ◁ (SSet.ι₀ : K ⟶ _)) ≫
        (α_ (Δ[1] : SSet.{u}) K (Δ[1] : SSet.{u})).inv =
      (SSet.ι₀ : (Δ[1] : SSet.{u}) ⊗ K ⟶ _) := rfl
    rw [← Category.assoc, hi, H.h₀]
    rfl
  h₁ := by
    apply intervalMappingUncurry_injective x y
    rw [intervalMappingUncurry_precomp, dgGluingIntervalUncurryHomotopyInverseMap,
      intervalMappingUncurry_curryOfEndpoints]
    have hi : ((Δ[1] : SSet.{u}) ◁ (SSet.ι₁ : K ⟶ _)) ≫
        (α_ (Δ[1] : SSet.{u}) K (Δ[1] : SSet.{u})).inv =
      (SSet.ι₁ : (Δ[1] : SSet.{u}) ⊗ K ⟶ _) := rfl
    rw [← Category.assoc, hi, H.h₁]
    rfl
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

end SerrePositivity.InfinityCategories
