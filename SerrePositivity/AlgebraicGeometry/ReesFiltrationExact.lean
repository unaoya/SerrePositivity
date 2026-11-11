module

public import SerrePositivity.AlgebraicGeometry.ReesFiltrationMaps

/-!
概要：次数ごとの全射性と完全性を Rees 加群へ移す。
方針：直和の全射性と、有限個の係数の持ち上げを使う。
規約：各次数の完全性を入力として明示する。
使われ方：I 進加群とその商の長完全列、Rees 加群の核の次数分解。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.AlgebraicGeometry

open scoped DirectSum BigOperators

variable {R M N P : Type*} [CommRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable [AddCommGroup P] [Module R P]
variable {I : Ideal R} (F : I.Filtration M) (G : I.Filtration N) (H : I.Filtration P)

/-- 各次数で全射な写像は、Rees 加群でも全射。 -/
theorem reesFiltrationMap_surjective (f : M →ₗ[R] N)
    (hf : ∀ n, ∀ m ∈ F.N n, f m ∈ G.N n)
    (hs : ∀ n, ∀ y ∈ G.N n, ∃ x : F.N n, f x.val = y) :
    Function.Surjective (reesFiltrationMap F G f hf) := by
  let l (n : ℕ) := (f.comp (F.N n).subtype).codRestrict (G.N n) (fun x ↦ hf n x.val x.property)
  have hl (n : ℕ) : Function.Surjective (l n) := by
    intro y
    obtain ⟨x, hx⟩ := hs n y.val y.property
    exact ⟨x, Subtype.ext hx⟩
  intro p
  obtain ⟨z, rfl⟩ := reesFiltrationAssemble_surjective G p
  obtain ⟨x, hx⟩ := (DirectSum.lmap_surjective l).mpr hl z
  refine ⟨reesFiltrationAssemble F x, ?_⟩
  rw [reesFiltrationMap_assemble, hx]

/-- 各次数で完全な二つの写像は、Rees 加群でも完全。 -/
theorem reesFiltrationMap_exact (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : ∀ n, ∀ m ∈ F.N n, f m ∈ G.N n)
    (hg : ∀ n, ∀ m ∈ G.N n, g m ∈ H.N n)
    (he : ∀ n, ∀ y ∈ G.N n, g y = 0 ↔ ∃ x : F.N n, f x.val = y) :
    Function.Exact (reesFiltrationMap F G f hf) (reesFiltrationMap G H g hg) := by
  classical
  intro y
  constructor
  · intro hy
    have hn (n : ℕ) : g (y.val.coeff n) = 0 := by
      have hc := congrArg (fun p : H.submodule ↦ p.val.coeff n) hy
      simpa only [reesFiltrationMap_coeff, Submodule.coe_zero,
        PolynomialModule.coeff_zero, Finsupp.zero_apply] using hc
    choose x hx using fun n ↦ (he n _ (y.property n)).mp (hn n)
    refine ⟨∑ n ∈ y.val.coeff.support, reesFiltrationSingle F n (x n), ?_⟩
    simp only [map_sum, reesFiltrationMap_single]
    calc
      ∑ n ∈ y.val.coeff.support, reesFiltrationSingle G n ⟨f (x n).val, hf n _ (x n).property⟩ =
          ∑ n ∈ y.val.coeff.support, reesFiltrationSingle G n ⟨y.val.coeff n, y.property n⟩ := by
        apply Finset.sum_congr rfl
        intro n _
        congr 1
        exact Subtype.ext (hx n)
      _ = y := reesFiltration_sum_single G y
  · rintro ⟨x, rfl⟩
    apply Subtype.ext
    apply PolynomialModule.coeff_injective
    ext n
    change g (f (x.val.coeff n)) = 0
    exact (he n _ (hf n _ (x.property n))).mpr ⟨⟨x.val.coeff n, x.property n⟩, rfl⟩

end SerrePositivity.AlgebraicGeometry
