module

public import Mathlib.Algebra.Module.LocalizedModule.Away

/-!
概要：b と ab の局所化の間の写像は a の局所化である。
方針：可逆な b の作用で分母を割り、核の分母を消去する。
規約：任意の加群と R 線形写像について存在を証明する。
使われ方：TT §3、Bondal–van den Bergh Thm 3.1.1、Toën §3.2 の基本開 Čech 計算。
-/

@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.DerivedGeometry
variable {R : Type u} [CommRing R]
  {M : Type v} [AddCommGroup M] [Module R M]
  {N : Type w} [AddCommGroup N] [Module R N]
  {L : Type z} [AddCommGroup L] [Module R L]

/--
概要：b の局所化から ab の局所化への線形比較は a の局所化。
方針：分母表示の b の冪を割り、核では b の冪の単射性を使う。
規約：比較写像と合成写像の実際の局所化の普遍性だけを入力とする。
使われ方：TT §3、Toën §3.2 の D(b) から D(ab) への切断の制限。
-/
theorem awayLocalization_of_composite (a b : R) (f : M →ₗ[R] N) (g : N →ₗ[R] L)
    [IsLocalizedModule.Away b f] [IsLocalizedModule.Away (a * b) (g ∘ₗ f)] :
    IsLocalizedModule.Away a g := by
  have hab := IsLocalizedModule.Away.isUnit_algebraMap (g ∘ₗ f) (a * b)
  rw [map_mul, (Algebra.commute_algebraMap_left _ _).isUnit_mul_iff] at hab
  have hbN (n : ℕ) : Function.Bijective (fun x : N => b ^ n • x) := by
    have hu : IsUnit (algebraMap R (Module.End R N) (b ^ n)) := by
      rw [map_pow]
      exact (IsLocalizedModule.Away.isUnit_algebraMap f b).pow n
    exact (Module.End.isUnit_iff _).mp hu
  have hbL (n : ℕ) : Function.Bijective (fun x : L => b ^ n • x) := by
    have hu : IsUnit (algebraMap R (Module.End R L) (b ^ n)) := by
      rw [map_pow]
      exact hab.2.pow n
    exact (Module.End.isUnit_iff _).mp hu
  apply IsLocalizedModule.Away.mk_of_addCommGroup hab.1
  · intro y
    obtain ⟨n, x, hx⟩ := IsLocalizedModule.Away.surj (g ∘ₗ f) (a * b) y
    obtain ⟨z, hz⟩ := (hbN n).surjective (f x)
    refine ⟨n, z, (hbL n).injective ?_⟩
    calc
      b ^ n • (a ^ n • y) = (a * b) ^ n • y := by
        rw [mul_pow, mul_smul, smul_comm]
      _ = g (f x) := hx
      _ = g (b ^ n • z) := congrArg g hz.symm
      _ = b ^ n • g z := g.map_smul _ _
  · intro x hx
    obtain ⟨k, m, hm⟩ := IsLocalizedModule.Away.surj f b x
    have hgm : (g ∘ₗ f) m = (g ∘ₗ f) 0 := by
      change g (f m) = g (f 0)
      rw [← hm, g.map_smul, hx, smul_zero, f.map_zero, g.map_zero]
    obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq (a * b) hgm
    have hn₀ : (a * b) ^ n • m = 0 := by simpa only [smul_zero] using hn
    have hf₀ : (a * b) ^ n • f m = 0 := by
      rw [← f.map_smul, hn₀, f.map_zero]
    refine ⟨n, (hbN (n + k)).injective ?_⟩
    calc
      b ^ (n + k) • (a ^ n • x) = (a * b) ^ n • (b ^ k • x) := by
        simp only [pow_add, mul_pow, mul_smul]
        rw [smul_comm (b ^ k) (a ^ n), smul_comm (b ^ n) (a ^ n)]
      _ = (a * b) ^ n • f m := congrArg ((a * b) ^ n • ·) hm
      _ = b ^ (n + k) • 0 := by rw [hf₀, smul_zero]

end SerrePositivity.KST.DerivedGeometry
