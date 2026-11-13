module

public import Mathlib.Algebra.Colimit.DirectLimit

/-!
概要：有限段の核の消滅と像の持ち上げから、加群の順極限の写像を全単射にする。
方針：順極限の元と零判定を有限段へ戻し、有向系の可換四角形を使う。
規約：自然数で添字付けした実際の線形写像の系を使う。
使われ方：F6 の Čech H の Frobenius 系に、2e の核・像評価を適用する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u v
variable {R : Type v} [CommRing R] {M N : ℕ → Type u}
variable [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
variable [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]
variable (f : ∀ i j, i ≤ j → M i →ₗ[R] M j)
variable (g : ∀ i j, i ≤ j → N i →ₗ[R] N j)
variable [DirectedSystem M (f · · ·)] [DirectedSystem N (g · · ·)]
variable (a : ∀ n, M n →ₗ[R] N n)
variable (ha : ∀ i j h x, a j (f i j h x) = g i j h (a i x))

/-- 可換な段ごとの線形写像が誘導する、実際の加群の順極限の線形写像。 -/
def linearDirectLimitComparison : DirectLimit M f →ₗ[R] DirectLimit N g :=
  DirectLimit.Module.lift R ℕ M f
    (fun n ↦ (DirectLimit.Module.of R ℕ N g n).comp (a n)) (by
      intro i j h x
      change DirectLimit.Module.of R ℕ N g j (a j (f i j h x)) =
        DirectLimit.Module.of R ℕ N g i (a i x)
      rw [ha]
      exact DirectLimit.Module.of_f)

/-- 順極限の比較は、有限段では指定した線形写像。 -/
theorem linearDirectLimitComparison_of (n : ℕ) (x : M n) :
    linearDirectLimitComparison f g a ha (DirectLimit.Module.of R ℕ M f n x) =
      DirectLimit.Module.of R ℕ N g n (a n x) := rfl

/-- 各段の核の元が後の段で消えるなら、順極限の比較は単射。 -/
theorem linearDirectLimitComparison_injective
    (hk : ∀ n (x : M n), a n x = 0 → ∃ m, ∃ h : n ≤ m, f n m h x = 0) :
    Function.Injective (linearDirectLimitComparison f g a ha) := by
  apply (injective_iff_map_eq_zero (linearDirectLimitComparison f g a ha)).mpr
  intro z hz
  obtain ⟨n, x, rfl⟩ := DirectLimit.exists_eq_mk f z
  change (⟦⟨n, a n x⟩⟧ : DirectLimit N g) = 0 at hz
  obtain ⟨m, hnm, hm⟩ := (DirectLimit.exists_eq_zero (f := g) ⟨n, a n x⟩).mp hz
  obtain ⟨k, hmk, hzero⟩ := hk m (f n m hnm x) ((ha n m hnm x).trans hm)
  apply (DirectLimit.exists_eq_zero (f := f) ⟨n, x⟩).mpr
  refine ⟨k, hnm.trans hmk, ?_⟩
  exact (DirectedSystem.map_map' f hnm hmk x).symm.trans hzero

/-- 標的の各元が後の段で像に入るなら、順極限の比較は全射。 -/
theorem linearDirectLimitComparison_surjective
    (hs : ∀ n (y : N n), ∃ m, ∃ h : n ≤ m, ∃ x : M m, a m x = g n m h y) :
    Function.Surjective (linearDirectLimitComparison f g a ha) := by
  intro z
  obtain ⟨n, y, rfl⟩ := DirectLimit.exists_eq_mk g z
  obtain ⟨m, hnm, x, hx⟩ := hs n y
  refine ⟨DirectLimit.Module.of R ℕ M f m x, ?_⟩
  rw [linearDirectLimitComparison_of, hx]
  exact DirectLimit.Module.of_f

end SerrePositivity.AlgebraicGeometry
