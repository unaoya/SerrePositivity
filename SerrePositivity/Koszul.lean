module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.Single
public import Mathlib.RingTheory.Length

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
係数つきの `K(x; M) = K(x; R) ⊗_R M` は各次数で `M` をテンソルしたもの。
-/

@[expose] public section

universe u

open CategoryTheory

namespace SerrePositivity

variable {R : Type u} [CommRing R]

/-- 複体 `K` の自己射 `a • 𝟙 K`。 -/
noncomputable def smulId (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ) : K ⟶ K :=
  a • 𝟙 K

/-- 列 `x : Fin n → R` の Koszul 複体 `K(x; R)`。`n` に関する再帰で、最後の元 `x (Fin.last n)` を
外側の写像錐にとる。 -/
noncomputable def koszulComplex : {n : ℕ} → (Fin n → R) → CochainComplex (ModuleCat.{u} R) ℤ
  | 0, _ =>
    (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj (ModuleCat.of R R)
  | n + 1, x =>
    CochainComplex.mappingCone (smulId (x (Fin.last n)) (koszulComplex (Fin.init x)))

/-- 係数 `M` の Koszul 複体 `K(x; M) = K(x; R) ⊗_R M`。 -/
noncomputable def koszulComplexCoeff {n : ℕ} (x : Fin n → R) (M : Type u) [AddCommGroup M]
    [Module R M] : CochainComplex (ModuleCat.{u} R) ℤ :=
  ((MonoidalCategory.tensorRight (ModuleCat.of R M)).mapHomologicalComplex _).obj (koszulComplex x)

/-- Koszul ホモロジー `H_i(x; M)`（homological 次数 `i`、cochain では `-i` 次）。 -/
noncomputable abbrev koszulHomology {n : ℕ} (x : Fin n → R) (M : Type u) [AddCommGroup M]
    [Module R M] (i : ℕ) : Type u :=
  (koszulComplexCoeff x M).homology (-(i : ℤ))

/-- `H_i(x; R)`：係数が `R` 自身の Koszul ホモロジー。 -/
noncomputable abbrev koszulHomologySelf {n : ℕ} (x : Fin n → R) (i : ℕ) : Type u :=
  (koszulComplex x).homology (-(i : ℤ))

end SerrePositivity
