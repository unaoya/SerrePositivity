module

public import SerrePositivity.NormalizedLength
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Ring.Action.Basic
public import Mathlib.Algebra.Ring.NegOnePow

/-!
# 閉点に台をもつ完全複体とその二つの Euler 評価（論文 §3.4、Lemma 3.5）

- `IsPerfectSupported J P`：`P` は有界で各項が有限自由な `T` 複体で、各ホモロジーが `J` の冪で消える。
  Lemma 3.5 では `J = m_A T`。
- `chiOrd T P = Σ_i (-1)^i length_T H_i(P)`：通常の Euler 評価。
- `chiLam λ φ P = Σ_i (-1)^i λ H_i(P ⊗_T C)`：正規化長さ `λ` による評価。`φ : T →+* C`。
- `twist g P = g^*P`：`g : T → T` に沿った係数制限（論文 §3.4 末尾の scalar twisting）。

添字は cochain で、homological な `i` 次は cochain の `-i` 次。符号 `(-1)^i` は `Int.negOnePow` で与える。
-/

@[expose] public section

universe u

open CategoryTheory

namespace SerrePositivity

variable {T : Type u} [CommRing T]

/-- `P` が閉点（`J` の零点集合）に台をもつ完全複体であること。 -/
structure IsPerfectSupported (J : Ideal T) (P : CochainComplex (ModuleCat.{u} T) ℤ) : Prop where
  /-- 有界。 -/
  bounded : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → Limits.IsZero (P.X i)
  /-- 各項は自由。 -/
  free : ∀ i, Module.Free T (P.X i)
  /-- 各項は有限生成。 -/
  finite : ∀ i, Module.Finite T (P.X i)
  /-- 各ホモロジーは `J` の冪で消える。 -/
  supported : ∀ i, ∃ n : ℕ, Module.IsTorsionBySet T (P.homology i) (J ^ n : Ideal T)

/-- 通常の Euler 評価 `χ_T(P) = Σ_i (-1)^i length_T H_i(P)`。無限長は `0` になる。 -/
noncomputable def chiOrd (P : CochainComplex (ModuleCat.{u} T) ℤ) : ℝ :=
  ∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * ((Module.length T (P.homology i)).toNat : ℝ)

variable {C : Type u} [CommRing C]

/-- 係数拡大 `P ⊗_T C`（`φ : T →+* C` に沿って）。 -/
noncomputable abbrev baseChange (φ : T →+* C) (P : CochainComplex (ModuleCat.{u} T) ℤ) :
    CochainComplex (ModuleCat.{u} C) ℤ :=
  ((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex _).obj P

/-- 正規化長さ `λ` による Euler 評価 `χ_C(P) = Σ_i (-1)^i λ H_i(P ⊗_T C)`。無限の長さは `0` になる。 -/
noncomputable def chiLam {J : Ideal C} (lam : NormalizedLength C J) (φ : T →+* C)
    (P : CochainComplex (ModuleCat.{u} T) ℤ) : ℝ :=
  ∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * (lam.len ((baseChange φ P).homology i)).toReal

variable {G : Type u} [Group G] [MulSemiringAction G T]

/-- ひねり `g^*P`：`g : T → T` に沿った係数制限。 -/
noncomputable abbrev twist (g : G) (P : CochainComplex (ModuleCat.{u} T) ℤ) :
    CochainComplex (ModuleCat.{u} T) ℤ :=
  ((ModuleCat.restrictScalars (MulSemiringAction.toRingHom G T g)).mapHomologicalComplex _).obj P

end SerrePositivity
