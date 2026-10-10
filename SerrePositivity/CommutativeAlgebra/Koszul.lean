module

public import SerrePositivity.HomologicalAlgebra.Basic
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.Length
public import SerrePositivity.HomologicalAlgebra.BaseChange
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Koszul 複体

列 `x = (x₀, …, xₙ₋₁)` の Koszul 複体 `K(x; R)` を、写像錐の反復で定義する：

- `K(∅) = R`（0 次に集中）
- `K(x₀, …, xₙ) = Cone(xₙ • 𝟙 : K(x₀, …, xₙ₋₁) → K(x₀, …, xₙ₋₁))`

これは `K(x) ≅ Cone(xₙ : K(x₀,…,xₙ₋₁) → K(x₀,…,xₙ₋₁))` という標準的な特徴づけそのもので、
最後の元を外側にとるので、正則列の帰納法（`xₙ` は `R/(x₀, …, xₙ₋₁)` 上で正則。Mathlib の
`RingTheory.Sequence.IsRegular` と同じ向き）にそのまま使える。

添字は cochain（`ComplexShape.up ℤ`）で、`K(x)` は `-n, …, 0` 次に乗る。
論文は homological に添字づけしているので、`H_i(x; M)` は cochain の `-i` 次のホモロジーである。
係数 `C` の Koszul ホモロジー `H_i(z; C)` は、`z` の像の Koszul 複体のホモロジー
`koszulHomologySelf (φ ∘ z) i` で書く（係数拡大との両立はこのファイルの後半）。

項の性質（正の次数と `-n` 次より下で零、各項は有限自由で射影的）と、`A` 上の長さで測った
Euler 標数 `koszulEulerChar` もここに置く。完全性は `KoszulResolution.lean`。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

variable {R : Type u} [CommRing R]

/-- 列 `x : Fin n → R` の Koszul 複体 `K(x; R)`。`n` に関する再帰で、最後の元 `x (Fin.last n)` を
外側の写像錐にとる。 -/
noncomputable def koszulComplex : {n : ℕ} → (Fin n → R) → CochainComplex (ModuleCat.{u} R) ℤ
  | 0, _ =>
    (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj (ModuleCat.of R R)
  | n + 1, x =>
    CochainComplex.mappingCone (smulId (x (Fin.last n)) (koszulComplex (Fin.init x)))

/-- `H_i(x; R)`：Koszul ホモロジー（homological 次数 `i`、cochain では `-i` 次）。 -/
noncomputable abbrev koszulHomologySelf {n : ℕ} (x : Fin n → R) (i : ℕ) : Type u :=
  (koszulComplex x).homology (-(i : ℤ))

/-- 空の列の Koszul 複体は、環自身を零次に置いた単一複体である。 -/
lemma koszulComplex_zero (x : Fin 0 → R) :
    koszulComplex x =
      (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj (ModuleCat.of R R) :=
  rfl

/-- 列の末尾に元を追加した Koszul 複体は、それまでの複体上の末尾の元による乗法の写像錐である。 -/
lemma koszulComplex_succ {n : ℕ} (x : Fin (n + 1) → R) :
    koszulComplex x =
      CochainComplex.mappingCone (smulId (x (Fin.last n)) (koszulComplex (Fin.init x))) :=
  rfl

/-! ## 項の性質 -/

/-- Koszul 複体は正の次数で零。 -/
lemma koszulComplex_isZero_X_of_pos :
    ∀ {n : ℕ} (x : Fin n → R) (i : ℤ), 0 < i → IsZero ((koszulComplex x).X i)
  | 0, x, i, hi => by
    rw [koszulComplex_zero]
    exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  | n + 1, x, i, hi => by
    rw [koszulComplex_succ, CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨koszulComplex_isZero_X_of_pos (Fin.init x) (i + 1) (by omega),
      koszulComplex_isZero_X_of_pos (Fin.init x) i hi⟩

/-- Koszul 複体は `-n` 次より下で零。 -/
lemma koszulComplex_isZero_X_of_lt :
    ∀ {n : ℕ} (x : Fin n → R) (i : ℤ), i < -(n : ℤ) → IsZero ((koszulComplex x).X i)
  | 0, x, i, hi => by
    rw [koszulComplex_zero]
    exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  | n + 1, x, i, hi => by
    rw [koszulComplex_succ, CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨koszulComplex_isZero_X_of_lt (Fin.init x) (i + 1) (by omega),
      koszulComplex_isZero_X_of_lt (Fin.init x) i (by omega)⟩

/-- Koszul 複体の項は有限自由。 -/
lemma koszulComplex_free_finite_X :
    ∀ {n : ℕ} (x : Fin n → R) (i : ℤ),
      Module.Free R ((koszulComplex x).X i) ∧ Module.Finite R ((koszulComplex x).X i)
  | 0, x, i => by
    rw [koszulComplex_zero]
    by_cases hi : i = 0
    · subst hi
      let e := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (ModuleCat.of R R)).toLinearEquiv
      exact ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm⟩
    · have h := HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
        (ModuleCat.of R R) i hi
      exact ⟨isZero_moduleCat_free h, isZero_moduleCat_finite h⟩
  | n + 1, x, i => by
    rw [koszulComplex_succ]
    obtain ⟨h1, h2⟩ := koszulComplex_free_finite_X (Fin.init x) (i + 1)
    obtain ⟨h3, h4⟩ := koszulComplex_free_finite_X (Fin.init x) i
    exact mappingCone_free_finite _ i

/-- Koszul 複体の各項は射影的（有限自由加群なので）。 -/
lemma koszulComplex_projective_X {n : ℕ} (x : Fin n → R) (i : ℤ) :
    Projective ((koszulComplex x).X i) :=
  projective_of_free (koszulComplex_free_finite_X x i).1

/-- Koszul 複体のホモロジーは正の次数で零。 -/
lemma koszulComplex_isZero_homology_of_pos {n : ℕ} (x : Fin n → R) (i : ℤ) (hi : 0 < i) :
    IsZero ((koszulComplex x).homology i) :=
  isZero_homology_of_isZero_X _ _ (koszulComplex_isZero_X_of_pos x i hi)

/-! ## `A` 上の長さで測った Euler 標数 -/

/-- `K(z; T) = K(z) ⊗_A T` の Euler 標数を `A` 上の長さで測ったもの
`χ^A(z; T) = Σ_i (-1)^i length_A H_i(z; T)`。`K(z; T)` は `T` の元 `z` の像の Koszul 複体で、
各ホモロジーを係数制限で `A` 加群とみる。`χ^A(z; T) = rank_A T`（正則局所環、Serre の定理）は
`Inputs/RegularLocalRing.lean` の入力。 -/
noncomputable def koszulEulerChar (A T : Type u) [CommRing A] [CommRing T] [Algebra A T] {e : ℕ}
    (z : Fin e → A) : ℝ :=
  ∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * ((Module.length A ((ModuleCat.restrictScalars
    (algebraMap A T)).obj ((koszulComplex (algebraMap A T ∘ z)).homology i))).toNat : ℝ)

end SerrePositivity

end

/-!
## Koszul 複体の基底変更

環準同型 `φ : A → C` による係数拡大（`baseChange φ`）は Koszul 複体と両立する：
`C ⊗_A K(z; A) ≅ K(φ z; C)`。写像錐の反復で定義したので、
写像錐が加法的関手と両立すること（`homotopyCofiber.mapHomologicalComplexObjIso`）と、
係数拡大が `a • 𝟙` を `φ a • 𝟙` に送ることから、`n` の帰納法で出る。
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped ChangeOfRings

namespace SerrePositivity

variable {A C : Type u} [CommRing A] [CommRing C] (φ : A →+* C)

/-- 基底変更と Koszul 複体の両立：`C ⊗_A K(z; A) ≅ K(φ z; C)`。 -/
noncomputable def baseChangeKoszulIso :
    ∀ {n : ℕ} (z : Fin n → A), baseChange φ (koszulComplex z) ≅ koszulComplex (φ ∘ z)
  | 0, z =>
    (HomologicalComplex.singleMapHomologicalComplex (ModuleCat.extendScalars.{u, u, u} φ)
      (c := ComplexShape.up ℤ) 0).app (ModuleCat.of A A) ≪≫
    (HomologicalComplex.single (ModuleCat.{u} C) (ComplexShape.up ℤ) 0).mapIso
      (letI := φ.toAlgebra; (TensorProduct.AlgebraTensorModule.rid A C C).toModuleIso)
  | n + 1, z => by
    change baseChange φ (CochainComplex.mappingCone
      (smulId (z (Fin.last n)) (koszulComplex (Fin.init z)))) ≅
      CochainComplex.mappingCone (smulId (φ (z (Fin.last n))) (koszulComplex (Fin.init (φ ∘ z))))
    refine HomologicalComplex.homotopyCofiber.mapHomologicalComplexObjIso _ _ ≪≫ ?_
    rw [baseChange_smulId]
    exact HomologicalComplex.homotopyCofiber.mapArrowIso _ _ (fun j ↦ ⟨j - 1, by simp⟩)
      (Arrow.isoMk (baseChangeKoszulIso (Fin.init z)) (baseChangeKoszulIso (Fin.init z))
        (by simp [smulId]))

end SerrePositivity

end
