module

public import SerrePositivity.HomologicalAlgebra.TorDimensionShift
public import SerrePositivity.CommutativeAlgebra.Length.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Flat.Basic
public import SerrePositivity.CommutativeAlgebra.Length.CommonResidueField

/-! # 二つの環の Tor の長さの比較

## 概要

`R → S` を環準同型（`S` は局所環で、剰余体は `R` からの像で尽くされる）、`R` は Noether 環とする。
`S` 加群 `N`、`R` 上平坦な `S` 加群 `D'`、`R` 加群 `D` と `R` 線形同型 `ε : N ⊗_S D' ≅ D` があり、
`Tor_{>0}^S(N, D') = 0` なら、有限生成 `R` 加群 `W` と全ての `n` について

\[
\ell_S \operatorname{Tor}_n^S(N, D' ⊗_R W) = \ell_R \operatorname{Tor}_n^R(D, W).
\]

## 方針

`n` についての帰納法（全ての `W` について同時に）。`W` を `0 → W' → R^m → W → 0` と表示し、
完全関手 `D' ⊗_R -` で移す。`Tor_{>0}^S(N, D'^m) = 0`、`Tor_{>0}^R(D, R^m) = 0` なので、

- `n = 0`：零次の Tor はテンソル積で、`N ⊗_S (D' ⊗_R W) ≅ (N ⊗_S D') ⊗_R W ≅ D ⊗_R W`。
- `n = 1`：両辺とも `Tor_1 ≅ ker(· ⊗ W' → · ⊗ R^m)` で、二つの核は上の自然な同型で対応する。
- `n ≥ 2`：両辺とも `Tor_n(W) ≅ Tor_{n-1}(W')` で、帰納法の仮定に帰着する。

途中の加群（`W'` のテンソル積など）が無限長でも、同型で比べるので問題ない。
`S` 上の長さと `R` 上の長さは剰余体が共通なので一致する（`length_eq_of_common_residueField`）。

## 使われ方

解説の付録 A（「引用している結果」の対角線論法の段落）の工程（次元シフトによる Tor の長さの比較）。
対角線の環 `S = R[[Y]]` で `N = S/(δ)`、`D' = S/PS`、`D = R/P` とし、
`Tor^R(R/P, R/Q)` を `Tor^S(S/(δ), T)` と比べる。
-/

@[expose] public section

universe u

open CategoryTheory TensorProduct IsLocalRing

namespace SerrePositivity

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
  (D' : Type u) [AddCommGroup D'] [Module S D'] [Module R D'] [IsScalarTower R S D']
  {D : Type u} [AddCommGroup D] [Module R D]
  (ε : N ⊗[S] D' ≃ₗ[R] D)

/-- 自然な同型 `N ⊗_S (D' ⊗_R W) ≅ D ⊗_R W`。 -/
noncomputable def tensorCompareEquiv (W : Type u) [AddCommGroup W] [Module R W] :
    N ⊗[S] (D' ⊗[R] W) ≃ₗ[R] D ⊗[R] W :=
  ((AlgebraTensorModule.assoc R S S N D' W).symm.restrictScalars R).trans
    (TensorProduct.congr ε (LinearEquiv.refl R W))

theorem tensorCompareEquiv_tmul (W : Type u) [AddCommGroup W] [Module R W]
    (n : N) (d : D') (w : W) :
    tensorCompareEquiv N D' ε W (n ⊗ₜ (d ⊗ₜ w)) = ε (n ⊗ₜ d) ⊗ₜ w := by
  simp [tensorCompareEquiv]

/-- 自然性：`W₁ → W₂` に沿って `tensorCompareEquiv` は可換。 -/
theorem tensorCompareEquiv_naturality {W₁ W₂ : Type u} [AddCommGroup W₁] [Module R W₁]
    [AddCommGroup W₂] [Module R W₂] (f : W₁ →ₗ[R] W₂) (x : N ⊗[S] (D' ⊗[R] W₁)) :
    tensorCompareEquiv N D' ε W₂ ((AlgebraTensorModule.lTensor S D' f).lTensor N x) =
      f.lTensor D (tensorCompareEquiv N D' ε W₁ x) := by
  induction x with
  | tmul n y =>
    induction y with
    | tmul d w => simp [tensorCompareEquiv_tmul]
    | add y z hy hz => simp only [tmul_add, map_add, hy, hz]
  | add x y hx hy => simp only [map_add, hx, hy]

section helpers

/-- `S` 加群の `S` 上の長さと `R` 上の長さは一致する。 -/
theorem length_S_eq_length_R [IsLocalRing S]
    (hres : Function.Surjective ((residue S).comp (algebraMap R S)))
    (X : Type u) [AddCommGroup X] [Module S X] [Module R X]
    [IsScalarTower R S X] : Module.length S X = Module.length R X :=
  (length_eq_of_common_residueField hres X).symm

/-- `Tor_{>0}^S(N, D' ⊗_R R^m) = 0`。 -/
theorem torModule_tensor_pi_subsingleton (N : Type u) [AddCommGroup N] [Module S N]
    (hTor : ∀ n, Subsingleton (TorModule S (n + 1) N D')) (m n : ℕ) :
    Subsingleton (TorModule S (n + 1) N (D' ⊗[R] (Fin m → R))) :=
  torModule_subsingleton_of_linearEquiv N (TensorProduct.piScalarRight R S D' (Fin m)).symm
    (n + 1) (torModule_pi_subsingleton N D' (n + 1) (hTor n) m)

/-- `Tor_{>0}^R(D, R^m) = 0`。 -/
theorem torModule_pi_self_subsingleton (D : Type u) [AddCommGroup D] [Module R D] (m n : ℕ) :
    Subsingleton (TorModule R (n + 1) D (Fin m → R)) := by
  have : Projective (ModuleCat.of R (Fin m → R)) := inferInstance
  exact ModuleCat.subsingleton_of_isZero
    (isZero_Tor_succ_of_projective (ModuleCat.{u} R) (ModuleCat.of R D) _ n)

end helpers

section main

variable [IsNoetherianRing R] [IsLocalRing S]
  (hres : Function.Surjective ((residue S).comp (algebraMap R S))) [Module.Flat R D']
  (hTor : ∀ n, Subsingleton (TorModule S (n + 1) N D'))

include hres hTor ε in
/-- **Tor の長さの比較**：有限生成 `R` 加群 `W` と全ての `n` について
`ℓ_S Tor_n^S(N, D' ⊗_R W) = ℓ_R Tor_n^R(D, W)`。自由加群による表示に沿った次元シフトによる。 -/
theorem length_torModule_tensor_eq (n : ℕ) :
    ∀ (W : Type u) [AddCommGroup W] [Module R W] [Module.Finite R W],
      Module.length S (TorModule S n N (D' ⊗[R] W)) = Module.length R (TorModule R n D W) := by
  induction n with
  | zero =>
    intro W _ _ _
    rw [(torModuleZeroEquiv S N (D' ⊗[R] W)).length_eq, length_S_eq_length_R hres,
      (tensorCompareEquiv N D' ε W).length_eq, (torModuleZeroEquiv R D W).length_eq]
  | succ n ih =>
    intro W _ _ _
    -- 自由加群による表示 `0 → W' → R^m → W → 0`
    obtain ⟨m, φ, hφ⟩ := Module.Finite.exists_fin' R W
    let W' := LinearMap.ker φ
    let f := W'.subtype
    have hf : Function.Injective f := W'.injective_subtype
    have hfφ : Function.Exact f φ := LinearMap.exact_subtype_ker_map φ
    -- `D' ⊗_R -` で移した短完全列
    let Φf := AlgebraTensorModule.lTensor S D' f
    let Φφ := AlgebraTensorModule.lTensor S D' φ
    have hΦf : Function.Injective Φf :=
      Module.Flat.lTensor_preserves_injective_linearMap (M := D') f hf
    have hΦφ : Function.Surjective Φφ := LinearMap.lTensor_surjective D' hφ
    have hΦ : Function.Exact Φf Φφ := lTensor_exact D' hfφ hφ
    cases n with
    | zero =>
      obtain ⟨eS⟩ := nonempty_torModule_one_equiv_ker N Φf Φφ hΦf hΦφ hΦ
        (torModule_tensor_pi_subsingleton D' N hTor m 0)
      obtain ⟨eR⟩ := nonempty_torModule_one_equiv_ker D f φ hf hφ hfφ
        (torModule_pi_self_subsingleton D m 0)
      rw [eS.length_eq, eR.length_eq, length_S_eq_length_R hres]
      -- 二つの核は自然な同型で対応する
      have hker : Submodule.map (tensorCompareEquiv N D' ε W').toLinearMap
          ((LinearMap.ker (Φf.lTensor N)).restrictScalars R) = LinearMap.ker (f.lTensor D) := by
        ext y
        simp only [Submodule.mem_map, Submodule.restrictScalars_mem, LinearMap.mem_ker,
          LinearEquiv.coe_coe]
        constructor
        · rintro ⟨x, hx, rfl⟩
          rw [← tensorCompareEquiv_naturality, show (Φf.lTensor N) x = 0 from hx, map_zero]
        · intro hy
          refine ⟨(tensorCompareEquiv N D' ε W').symm y, ?_, by simp⟩
          apply (tensorCompareEquiv N D' ε (Fin m → R)).injective
          rw [map_zero]
          change tensorCompareEquiv N D' ε (Fin m → R) ((Φf.lTensor N)
            ((tensorCompareEquiv N D' ε W').symm y)) = 0
          rw [tensorCompareEquiv_naturality, LinearEquiv.apply_symm_apply, hy]
      rw [← hker]
      exact ((Submodule.restrictScalarsEquiv R S _ _).restrictScalars R).symm.length_eq.trans
        (Submodule.equivMapOfInjective _ (tensorCompareEquiv N D' ε W').injective _).length_eq
    | succ n =>
      obtain ⟨eS⟩ := nonempty_torModule_succ_equiv N Φf Φφ hΦf hΦφ hΦ n
        (torModule_tensor_pi_subsingleton D' N hTor m (n + 1))
        (torModule_tensor_pi_subsingleton D' N hTor m n)
      obtain ⟨eR⟩ := nonempty_torModule_succ_equiv D f φ hf hφ hfφ n
        (torModule_pi_self_subsingleton D m (n + 1)) (torModule_pi_self_subsingleton D m n)
      have : Module.Finite R W' := inferInstance
      rw [eS.length_eq, eR.length_eq]
      exact ih W'

end main

end SerrePositivity
