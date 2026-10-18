module

public import SerrePositivity.KST.ProExcision.SpectralPro
public import Mathlib.RingTheory.Noetherian.Defs

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

/-!
# 冪作用の核の pro-消滅

概要：有限加群上の a 冪 torsion を、末尾変数の冪遷移で一様に消す。
方針：増大する冪核の安定化と、遷移が a の冪倍であることを使う。
規約：元環での a の正則性は仮定しない。
使われ方：KST Lemma 4.9 の境界次数と Lemma 4.10 の cone 長完全列。
-/

universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]

/-- 概要：aⁿ 倍の核。方針：スカラー線形写像の核として定義する。
規約：n=0 の核は零。使われ方：KST Lemma 4.9 の末尾変数の torsion。 -/
def powerKernel (a : R) (M : ModuleCat.{u} R) (n : ℕ) : Submodule R M :=
  (a ^ n • (LinearMap.id : M →ₗ[R] M)).ker

/-- 概要：冪作用の核は指数とともに増大する。
方針：大きい冪を小さい冪の倍として分解する。
規約：任意の加群に成立。使われ方：KST Lemma 4.9 の核の安定化。 -/
theorem powerKernel_mono (a : R) (M : ModuleCat.{u} R) : Monotone (powerKernel a M) := by
  intro n m h x hx
  change a ^ n • x = 0 at hx
  change a ^ m • x = 0
  rw [← Nat.sub_add_cancel h, pow_add, mul_smul, hx, smul_zero]

/-- 概要：Noether 加群の a 冪 torsion は一つの冪で全て消える。
方針：冪核の増大列を安定化し、小さい指数は単調性で扱う。
規約：指数は元に依存しない。使われ方：KST Lemma 4.9・4.10 の pro-零化。 -/
theorem exists_power_torsion_bound (a : R) (M : ModuleCat.{u} R) [IsNoetherian R M] :
    ∃ N : ℕ, ∀ n (x : M), a ^ n • x = 0 → a ^ N • x = 0 := by
  obtain ⟨N, hN⟩ := monotone_stabilizes_iff_noetherian.mpr
    (inferInstance : IsNoetherian R M) ⟨powerKernel a M, powerKernel_mono a M⟩
  refine ⟨N, fun n x hx ↦ ?_⟩
  by_cases h : n ≤ N
  · exact powerKernel_mono a M h hx
  · have he : powerKernel a M N = powerKernel a M n := hN n (by omega)
    have hx' : x ∈ powerKernel a M n := hx
    rw [← he] at hx'
    exact hx'

/-- 概要：冪核間の遷移は aᵐ⁻ⁿ 倍である。
方針：aⁿ 倍との合成を aᵐ 倍へまとめる。
規約：n≤m。使われ方：KST Lemma 4.9 の原典と同じ冪遷移。 -/
def powerKernelTransition (a : R) (M : ModuleCat.{u} R) {m n : ℕ} (h : n ≤ m) :
    ModuleCat.of R (powerKernel a M m) ⟶ ModuleCat.of R (powerKernel a M n) :=
  ModuleCat.ofHom
    { toFun := fun x ↦ ⟨a ^ (m - n) • x.val, by
        change a ^ n • (a ^ (m - n) • x.val) = 0
        rw [← mul_smul, ← pow_add, Nat.add_sub_of_le h]
        exact x.property⟩
      map_add' := fun x y ↦ Subtype.ext (smul_add _ _ _)
      map_smul' := fun r x ↦ Subtype.ext (smul_comm _ _ _) }

/-- 概要：冪核と冪倍遷移から実際の塔を作る。
方針：スカラーの指数の加法則で合成律を確認する。
規約：核の包含とは逆向き。使われ方：KST Lemma 4.9・4.10 の核の pro 系。 -/
def powerKernelTower (a : R) (M : ModuleCat.{u} R) : Tower (ModuleCat.{u} R) where
  obj n := ModuleCat.of R (powerKernel a M n)
  transition h := powerKernelTransition a M h
  transition_self n := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp [powerKernelTransition]
  transition_comp {k m n} hm hn := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change a ^ (m - n) • (a ^ (k - m) • x.val) = a ^ (k - n) • x.val
    rw [← mul_smul, ← pow_add, show m - n + (k - m) = k - n by omega]

/-- 概要：Noether 加群の冪核の塔は pro-零。
方針：共通 torsion 指数 N に対し、n+N 段から n 段への遷移を消す。
規約：N は n にも依存しない。使われ方：KST Lemma 4.9・4.10 の長完全列の核項。 -/
theorem powerKernelTower_isProZero (a : R) (M : ModuleCat.{u} R) [IsNoetherian R M] :
    IsProZero (powerKernelTower a M) := by
  obtain ⟨N, hN⟩ := exists_power_torsion_bound a M
  intro n
  refine ⟨n + N, Nat.le_add_right n N, ?_⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change a ^ (n + N - n) • x.val = 0
  rw [Nat.add_sub_cancel_left]
  exact hN (n + N) x.val x.property

end SerrePositivity.KST.ProExcision
