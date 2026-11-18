module

public import SerrePositivity.AlgebraicGeometry.AffineGammaFrobeniusCechExact
public import Mathlib.AlgebraicGeometry.Limits

/-!
概要：平坦全射の有限アフィン開族の合成を、同じアフィン射の係数へ渡す。
方針：同じ族の余積のアフィン性、平坦性、元の被覆性を使う。
規約：元の非アフィンな始域の大域切断の平坦性は仮定しない。
使われ方：同じ二重 Čech の行を有限アフィン族で計算する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
universe u
variable {Y S : Scheme.{u}} (f : Y ⟶ S)
variable {ι : Type} {Z : ι → Scheme.{u}} (g : ∀ i, Z i ⟶ Y)

/-- 元の被覆族と全射の合成は、同じ余積射として全射。 -/
theorem finiteOpenFamilyComposite_surjective [Surjective f]
    (hg : ⋃ i, Set.range (g i) = Set.univ) :
    Surjective (Sigma.desc (fun i ↦ g i ≫ f)) := by
  apply Surjective.sigmaDesc_of_union_range_eq_univ
  apply Set.eq_univ_of_forall
  intro s
  obtain ⟨y, hy⟩ := f.surjective s
  have hymem : y ∈ ⋃ i, Set.range (g i) := by rw [hg]; trivial
  obtain ⟨i, z, hz⟩ := Set.mem_iUnion.mp hymem
  refine Set.mem_iUnion.mpr ⟨i, z, ?_⟩
  simpa only [Scheme.Hom.comp_apply, hz] using hy

/-- 同じ有限アフィン開族の合成の Γ の実際の Frobenius 係数の増大 Čech は完全。 -/
theorem finiteAffineOpenFamilyFrobeniusCech_exact [Finite ι] [∀ i, IsAffine (Z i)]
    [∀ i, IsOpenImmersion (g i)] [IsAffine S] [Flat f] [Surjective f]
    (hg : ⋃ i, Set.range (g i) = Set.univ)
    (p : ℕ) (hp : p.Prime) (hS : (p : Γ(S, ⊤)) = 0) :
    SerrePositivity.Cech.AugmentedRingCechExact
      (frobeniusAugmentedRingCoefficients
        (Arrow.mk (Scheme.Γ.map (Sigma.desc (fun i ↦ g i ≫ f)).op)) p hp hS) := by
  haveI : Surjective (Sigma.desc (fun i ↦ g i ≫ f)) :=
    finiteOpenFamilyComposite_surjective f g hg
  haveI (i : ι) : Flat (g i ≫ f) := inferInstance
  exact affineGammaFrobeniusCech_exact_of_flat_surjective
    (Sigma.desc (fun i ↦ g i ≫ f)) p hp hS

end SerrePositivity.AlgebraicGeometry
