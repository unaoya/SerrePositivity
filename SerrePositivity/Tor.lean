module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.RingTheory.Length

/-!
# `Tor` を `R` 加群として見る

Mathlib の `CategoryTheory.Tor (ModuleCat R) i` は `X ⊗ -` の左導来関手（第 2 変数で導来）である。
ここではその対象を `R` 加群の型として取り出し、`Module.length` をとる。

規約（`notes/PLAN.md` §1.3）：`Tor ≅ Tor'`（対称性）は Mathlib に未証明なので、
このプロジェクトでは Tor の対称性を使わない。
-/

@[expose] public section

open CategoryTheory

universe u

namespace SerrePositivity

variable (R : Type u) [CommRing R]

/-- `Tor_i^R(M, N)` を `R` 加群の型として見たもの。
`CategoryTheory.Tor (ModuleCat R) i` の対象の台集合で、第 2 変数 `N` の射影分解で計算される。 -/
noncomputable abbrev TorModule (i : ℕ) (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] : Type u :=
  ((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R M)).obj (ModuleCat.of R N)

/-- `length_R Tor_i^R(M, N)`（`ℕ∞` 値）。 -/
noncomputable def torLength (i : ℕ) (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] : ℕ∞ :=
  Module.length R (TorModule R i M N)

end SerrePositivity

namespace SerrePositivity

variable {R : Type u} [CommRing R]

/-- 係数拡大関手は（係数制限関手の左随伴なので）加法的。左導来関手をとるのに要る。 -/
instance {C : Type u} [CommRing C] (φ : R →+* C) : (ModuleCat.extendScalars.{u, u, u} φ).Additive :=
  (ModuleCat.extendRestrictScalarsAdj φ).left_adjoint_additive

/-- `R` 代数 `C`（構造は環準同型 `φ : R →+* C` で与える）と `R` 加群 `N` に対する
`Tor_i^R(C, N)` を、係数拡大関手 `N ↦ C ⊗_R N : ModuleCat R ⥤ ModuleCat C` の
左導来関手として定め、`C` 加群の型として見たもの。
`φ` を取り替えることで、§5.1 の `ι_σ` によるひねりを表せる。 -/
noncomputable abbrev TorAlg {C : Type u} [CommRing C] (φ : R →+* C) (i : ℕ)
    (N : Type u) [AddCommGroup N] [Module R N] : Type u :=
  ((ModuleCat.extendScalars φ).leftDerived i).obj (ModuleCat.of R N)

end SerrePositivity
