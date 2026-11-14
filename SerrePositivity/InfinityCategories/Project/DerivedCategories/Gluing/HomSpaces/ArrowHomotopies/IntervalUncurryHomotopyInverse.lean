module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceIntervalComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.ArrowHomotopies.IntervalUncurryHomotopyBoundary

/-! 両側辺を固定する同じ実円柱を、区間 Hom 族のホモトピーへ戻す。 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
variable {K X : SSet.{u}} {x y : X _⦋0⦌}
  {f g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y}
  (H : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry g))
  (hx : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ▷ (Δ[1] : SSet.{u})) ≫ H.h = SSet.const x)
  (hy : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ▷ (Δ[1] : SSet.{u})) ≫ H.h = SSet.const y)

def dgGluingIntervalUncurryHomotopyInverseMap : K ⊗ (Δ[1] : SSet.{u}) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingCurryOfEndpoints
    ((α_ (Δ[1] : SSet.{u}) K (Δ[1] : SSet.{u})).inv ≫ H.h) (by
      have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (K ⊗ (Δ[1] : SSet.{u})) ≫
          (α_ (Δ[1] : SSet.{u}) K (Δ[1] : SSet.{u})).inv =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ▷ (Δ[1] : SSet.{u}) := rfl
      rw [← Category.assoc, hi, hx]) (by
      have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (K ⊗ (Δ[1] : SSet.{u})) ≫
          (α_ (Δ[1] : SSet.{u}) K (Δ[1] : SSet.{u})).inv =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ▷ (Δ[1] : SSet.{u}) := rfl
      rw [← Category.assoc, hi, hy])

lemma dgGluingIntervalUncurryHomotopyInverseMap_evaluate :
    (α_ (Δ[1] : SSet.{u}) K (Δ[1] : SSet.{u})).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (dgGluingIntervalUncurryHomotopyInverseMap H hx hy) = H.h := by
  rw [dgGluingIntervalUncurryHomotopyInverseMap,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_curryOfEndpoints, Iso.hom_inv_id_assoc]

def dgGluingIntervalUncurryHomotopyInverse : SSet.Homotopy f g where
  h := dgGluingIntervalUncurryHomotopyInverseMap H hx hy
  h₀ := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective x y
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, dgGluingIntervalUncurryHomotopyInverseMap,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_curryOfEndpoints]
    have hi : ((Δ[1] : SSet.{u}) ◁ (SSet.ι₀ : K ⟶ _)) ≫
        (α_ (Δ[1] : SSet.{u}) K (Δ[1] : SSet.{u})).inv =
      (SSet.ι₀ : (Δ[1] : SSet.{u}) ⊗ K ⟶ _) := rfl
    rw [← Category.assoc, hi, H.h₀]
    rfl
  h₁ := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective x y
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, dgGluingIntervalUncurryHomotopyInverseMap,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_curryOfEndpoints]
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

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
