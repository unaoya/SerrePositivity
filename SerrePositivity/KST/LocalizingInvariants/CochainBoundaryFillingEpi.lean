module

public import SerrePositivity.DifferentialGraded.Resolution.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
概要：全境界 cell の実充填から、複体射の各次数の全射性を導く。
方針：まず標的元の微分を零境界の cell で持ち上げ、次の cell で元自身を持ち上げる。
規約：充填条件は適用先で構成する。使われ方：実 cell augmentation の全射性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants
variable {R : Type u} [CommRing R] {K L : Complex R} (f : K ⟶ L)

lemma cochain_surjective_of_boundaryFilling
    (h : ∀ c : ComplexBoundaryCell R f, c.HasFilling R) (n : ℤ) :
    Function.Surjective (f.f n) := by
  intro b
  let c₀ : ComplexBoundaryCell R f := {
    degree := n + 1
    cycle := 0
    primitive := L.d n (n + 1) b
    boundary := by
      have hd := congrArg (fun g ↦ g b) (L.d_comp_d n (n + 1) (n + 1 + 1))
      change L.d (n + 1) (n + 1 + 1) (L.d n (n + 1) b) = 0 at hd
      change L.d (n + 1) (n + 1 + 1) (L.d n (n + 1) b) = f.f _ 0
      rw [map_zero]
      exact hd }
  obtain ⟨t, ht, hp⟩ := h c₀
  have hz : K.d (n + 1) (n + 1 + 1) t = 0 := ht
  let z : complexCycles R K (n + 1) := ⟨t, hz⟩
  let c : ComplexBoundaryCell R f := ⟨n, z, b, hp.symm⟩
  obtain ⟨a, _, ha⟩ := h c
  exact ⟨a, ha⟩

lemma cochain_component_epi_of_boundaryFilling
    (h : ∀ c : ComplexBoundaryCell R f, c.HasFilling R) (n : ℤ) : Epi (f.f n) :=
  (ModuleCat.epi_iff_surjective _).2 (cochain_surjective_of_boundaryFilling f h n)

end SerrePositivity.KST.LocalizingInvariants
