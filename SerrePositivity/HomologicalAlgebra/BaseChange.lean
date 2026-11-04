module

public import SerrePositivity.HomologicalAlgebra.Complex.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# 複体の係数拡大

## 概要

環準同型 `φ : T →+* C` に沿った係数拡大 `M ↦ C ⊗_T M`（Mathlib の `ModuleCat.extendScalars φ`）を
複体の各項に施す操作 `baseChange φ P = P ⊗_T C` を定め、基本的な性質を示す。論文では、`T` 複体 `P`
の `C` 上の正規化長さによる Euler 評価 `χ_C(P)` を `P ⊗_T C` のホモロジーで定義し
（`PerfectComplex/Basic.lean` の `chiLam`）、また Koszul 複体や射影分解の係数を `A` から `T`、`C` へ
拡大して比較する。そのための共通の道具である。

## 内容

- 係数拡大関手は加法的（`instance`）。関手を複体に項ごとに施す（`mapHomologicalComplex`）には
  加法性が必要で、左導来関手 `Tor`（`Tor.lean`）をとるときにも要る。係数制限関手の左随伴である
  ことから出る。
- `baseChange φ P`：各項を係数拡大した複体。有界性と「正の次数で零」を保つ
  （`baseChange_bounded`、`baseChange_isZero_X_of_pos`）。零対象は零対象に移るから。
- 係数拡大はスカラー倍を `φ` 倍に送る：加群の射について `F(a • f) = φ(a) • F(f)`
  （`extendScalars_map_smul`）、複体の射についても同様（`extendScalars_mapHomologicalComplex_smul`）、
  特に `a • 𝟙 K` は `φ(a) • 𝟙 (K ⊗ C)` に移る（`baseChange_smulId`）。Koszul 複体の基底変更
  `K(z) ⊗_A C ≅ K(φ z)`（`CommutativeAlgebra/Koszul/Resolution.lean`）、台の条件が基底変更で
  保たれること（`PerfectComplex/Support.lean`）、Tor の消去イデアル（`Tor.lean`）に使う。
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped ChangeOfRings

namespace SerrePositivity

section

variable {T C : Type u} [CommRing T] [CommRing C]

/-- 係数拡大関手 `extendScalars φ` は加法的である。係数制限関手 `restrictScalars φ` の左随伴なので
（`extendRestrictScalarsAdj`）、Mathlib の「左随伴は加法的」から出る。複体に項ごとに施すとき
（`mapHomologicalComplex`）と左導来関手をとるときの前提になる。 -/
instance (φ : T →+* C) : (ModuleCat.extendScalars.{u, u, u} φ).Additive :=
  (ModuleCat.extendRestrictScalarsAdj φ).left_adjoint_additive

/-- `T` 上の複体 `P` の、`φ : T →+* C` に沿った係数拡大 `P ⊗_T C`。各項に `extendScalars φ` を
施した `C` 上の複体で、`i` 次の項は `C ⊗_T P^i`、微分は `1 ⊗ d`。 -/
noncomputable abbrev baseChange (φ : T →+* C) (P : CochainComplex (ModuleCat.{u} T) ℤ) :
    CochainComplex (ModuleCat.{u} C) ℤ :=
  ((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex _).obj P

/-- `P` が `a` 次から `b` 次の範囲に乗っていれば、`baseChange φ P` も同じ範囲に乗る。零対象は
関手で零対象に移るから。台つき完全複体の有界性が基底変更で保たれること
（`PerfectComplex/Closure.lean`）に使う。 -/
lemma baseChange_bounded (φ : T →+* C) (P : CochainComplex (ModuleCat.{u} T) ℤ)
    (hP : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (P.X i)) :
    ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero ((baseChange φ P).X i) := by
  obtain ⟨a, b, hab⟩ := hP
  exact ⟨a, b, fun i hi ↦ (ModuleCat.extendScalars φ).map_isZero (hab i hi)⟩

/-- `K` が正の次数で零なら、`baseChange φ K` も正の次数で零。分解（`IsResolutionOf`）を基底変更
しても `0` 以下の次数に乗ることを言うのに使う（`Tor.lean` の `torIsoCochain`）。 -/
lemma baseChange_isZero_X_of_pos (φ : T →+* C) (K : CochainComplex (ModuleCat.{u} T) ℤ)
    (hK : ∀ i : ℤ, 0 < i → IsZero (K.X i)) (i : ℤ) (hi : 0 < i) :
    IsZero ((baseChange φ K).X i) :=
  (ModuleCat.extendScalars.{u, u, u} φ).map_isZero (hK i hi)

end

variable {A C : Type u} [CommRing A] [CommRing C] (φ : A →+* C)

/-- 係数拡大関手は、加群の射の `a` 倍を `φ(a)` 倍に送る：`F(a • f) = φ(a) • F(f)`。
`C ⊗_A N` は `1 ⊗ n` の形の元で生成され、`1 ⊗ (a • n) = φ(a) ⊗ n = φ(a) • (1 ⊗ n)` だから。
テンソル積の `ext` で生成元について確かめる。 -/
lemma extendScalars_map_smul {M N : ModuleCat.{u} A} (f : M ⟶ N) (a : A) :
    (ModuleCat.extendScalars.{u, u, u} φ).map (a • f) =
      φ a • (ModuleCat.extendScalars.{u, u, u} φ).map f := by
  ext m
  change ((1 : C) ⊗ₜ[A, φ] (a • f m) : (ModuleCat.extendScalars φ).obj N) =
    (φ a * 1) ⊗ₜ[A, φ] f m
  let _ : Module A C := Module.compHom C φ
  change (1 : C) ⊗ₜ[A] (a • f m) = (φ a * 1) ⊗ₜ[A] f m
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  rfl

/-- 複体の射についても、係数拡大は `a` 倍を `φ(a)` 倍に送る（添字の形 `c` は任意）。各成分で
`extendScalars_map_smul` を使う。 -/
lemma extendScalars_mapHomologicalComplex_smul {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex (ModuleCat.{u} A) c} (f : K ⟶ L) (a : A) :
    ((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex c).map (a • f) =
      φ a • ((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex c).map f := by
  ext i
  simp [extendScalars_map_smul]

/-- 複体の `a` 倍写像 `smulId a K = a • 𝟙 K` は、係数拡大で `baseChange φ K` の `φ(a)` 倍写像に移る。
Koszul 複体 `Cone(x_n • 𝟙 K')` の基底変更が `Cone(φ(x_n) • 𝟙 (K' ⊗ C))` になること
（`CommutativeAlgebra/Koszul/Resolution.lean` の `baseChangeKoszulIso`）の帰納段で使う。 -/
lemma baseChange_smulId (K : CochainComplex (ModuleCat.{u} A) ℤ) (a : A) :
    ((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex _).map (smulId a K) =
      smulId (φ a) (baseChange φ K) := by
  ext i
  simp [smulId, extendScalars_map_smul]

end SerrePositivity
