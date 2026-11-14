module

public import SerrePositivity.HomologicalAlgebra.TorSymmetry
public import SerrePositivity.CommutativeAlgebra.Koszul.Resolution
public import SerrePositivity.CommutativeAlgebra.Length.Basic
public import SerrePositivity.CommutativeAlgebra.Length.CommonResidueField

/-! # Koszul ホモロジーの長さを基底環上の Tor で表す

## 概要

`T` を局所環で、`R → T → T/m_T` が全射（剰余体が共通）とする。`R` の列 `z` の Koszul 複体が
`R/(z)` の分解なら、`T` の像の列の Koszul ホモロジーの `T` 上の長さは
`Tor_i^R(R/(z), T)` の `R` 上の長さに等しい。

## 方針

`K(z)` を `T` へ係数拡大すると `K(z; T)` になり（`baseChangeKoszulIso`）、
その係数制限したホモロジーは `Tor_i^R(T, R/(z))` と線形同値である（`ordinaryTorIso`）。
Tor の変数を交換し（`torModuleComm`）、剰余体が共通なので `T` 上と `R` 上の長さは一致する。

## 使われ方

Paper Theorem 2.5 の式 (2.4) の等標数部分で、高次 Koszul ホモロジーの消滅に用いるTor 長の評価。
`R = k[[Z]]` と `z = Z^q` にとり、`D` のパラメータの冪の Koszul ホモロジーを、
`q` によらない分解で計算できる `Tor_i^R(R/(Z^q), D)` に移す。
-/

@[expose] public section

universe u

open CategoryTheory IsLocalRing

namespace SerrePositivity

variable {R T : Type u} [CommRing R] [CommRing T] [Algebra R T] [IsLocalRing T]
  (hres : Function.Surjective ((residue T).comp (algebraMap R T)))

include hres in
/-- **Koszul ホモロジーと Tor の長さ**：`K(z)` が `R/(z)` の分解で、剰余体が共通なら
`ℓ_T H_i(z; T) = ℓ_R Tor_i^R(R/(z), T)`。係数拡大した Koszul 分解で Tor を計算し、変数を交換する。 -/
theorem length_koszulHomologySelf_eq_length_torModule {n : ℕ} (z : Fin n → R)
    (hz : IsKoszulResolution z) (i : ℕ) :
    Module.length T (koszulHomologySelf (algebraMap R T ∘ z) i) =
      Module.length R (TorModule R i (R ⧸ Ideal.span (Set.range z)) T) := by
  let U := ModuleCat.restrictScalars (algebraMap R T)
  -- 係数拡大した Koszul 複体と、Koszul 複体のホモロジーの比較
  let eK := (HomologicalComplex.homologyFunctor _ _ (-(i : ℤ))).mapIso
    (baseChangeKoszulIso (algebraMap R T) z)
  let e₁ : U.obj ((koszulComplex (algebraMap R T ∘ z)).homology (-(i : ℤ))) ≃ₗ[R]
      U.obj ((baseChange (algebraMap R T) (koszulComplex z)).homology (-(i : ℤ))) :=
    (U.mapIso eK.symm).toLinearEquiv
  let e₂ := ordinaryTorIso (R := R) (T := T) (R ⧸ Ideal.span (Set.range z)) (koszulComplex z)
    (isResolutionOf_koszul z hz) i
  let e₃ := torModuleComm (R := R) i T (R ⧸ Ideal.span (Set.range z))
  rw [← length_restrictScalars_eq hres, (e₁.trans (e₂.trans e₃)).length_eq]

end SerrePositivity
