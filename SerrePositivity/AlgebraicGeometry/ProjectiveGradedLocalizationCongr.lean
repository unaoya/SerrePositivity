module

public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedLocalizationMaps
public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedLocalizedDirectSum

/-!
概要：指定された分子の部分を対応させる線形同値を、斉次局所化へ制限する。
方針：両方向の斉次局所化写像を作り、合成と恒等写像の公式を適用する。
規約：分子の族には単調性や有限生成性を仮定しない。
使われ方：Rees 加群の次数成分の比較を標準開の切断へ移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
variable [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- 分子の指定部分を対応させる線形同値は、斉次局所化の同値を与える。 -/
def projectiveGradedAwayCongr (f : S) (e : M ≃ₗ[S] N)
    (V : ℕ → Submodule R M) (W : ℕ → Submodule R N)
    (he : ∀ k x, e x ∈ W k ↔ x ∈ V k) :
    projectiveGradedAway f V ≃ₗ[R] projectiveGradedAway f W := by
  let h₁ : ∀ k x, x ∈ V k → e x ∈ W k := fun k x hx ↦ (he k x).mpr hx
  let h₂ : ∀ k y, y ∈ W k → e.symm y ∈ V k := fun k y hy ↦
    (he k (e.symm y)).mp (by simpa only [e.apply_symm_apply] using hy)
  refine LinearEquiv.ofLinearMap
    (projectiveGradedAwayMap f V W e.toLinearMap h₁)
    (projectiveGradedAwayMap f W V e.symm.toLinearMap h₂) ?_ ?_
  · rw [← projectiveGradedAwayMap_comp]
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    change IsLocalizedModule.map (Submonoid.powers f)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) N)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) N)
      (e.toLinearMap.comp e.symm.toLinearMap) z.val = z.val
    rw [LinearEquiv.comp_symm, IsLocalizedModule.map_id]
    rfl
  · rw [← projectiveGradedAwayMap_comp]
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    change IsLocalizedModule.map (Submonoid.powers f)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
      (e.symm.toLinearMap.comp e.toLinearMap) z.val = z.val
    rw [LinearEquiv.symm_comp, IsLocalizedModule.map_id]
    rfl

/-- 斉次局所化の比較の値は、周囲の局所化の誘導写像の値。 -/
theorem projectiveGradedAwayCongr_val (f : S) (e : M ≃ₗ[S] N)
    (V : ℕ → Submodule R M) (W : ℕ → Submodule R N)
    (he : ∀ k x, e x ∈ W k ↔ x ∈ V k) (z : projectiveGradedAway f V) :
    (projectiveGradedAwayCongr f e V W he z).val =
      IsLocalizedModule.map (Submonoid.powers f)
        (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
        (LocalizedModule.mkLinearMap (Submonoid.powers f) N) e.toLinearMap z.val := rfl

section DirectSum

open scoped DirectSum
variable {κ : Type*} [DecidableEq κ]
variable {F : κ → Type*} [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)]
variable [∀ i, Module S (F i)] [∀ i, IsScalarTower R S (F i)]

/-- 分子の次数を保つ直和との同値を、斉次局所化の直和比較へ移す。 -/
def projectiveGradedLocalizedDirectSumTransport (f : S)
    (V : ∀ i, ℕ → Submodule R (F i)) (W : ℕ → Submodule R N)
    (e : (⨁ i, F i) ≃ₗ[S] N)
    (he : ∀ k x, e x ∈ W k ↔ x ∈ projectiveDirectSumSubmodule (fun i ↦ V i k))
    (hstep : ∀ (i : κ) (k : ℕ) (m : V i k), f • m.val ∈ V i (k + 1)) :
    projectiveGradedAway f W ≃ₗ[R] ⨁ i, projectiveGradedAway f (V i) :=
  (projectiveGradedAwayCongr f e
    (fun k ↦ projectiveDirectSumSubmodule (fun i ↦ V i k)) W he).symm.trans
      (projectiveGradedLocalizedDirectSumLinearEquiv f V hstep)

end DirectSum

end SerrePositivity.AlgebraicGeometry
