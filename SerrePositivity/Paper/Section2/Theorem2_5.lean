module

public import SerrePositivity.CommutativeAlgebra.HilbertSamuel
public import SerrePositivity.CommutativeAlgebra.Koszul
public import SerrePositivity.Paper.Section2.TowerLength
public import SerrePositivity.PerfectComplex.NormalizedLengthComap
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Theorem 2.5（正規化長さの入力）

## 概要

論文 Theorem 2.5：Lemma 2.2 の `(D, 𝔡, k)` と基底 `A ⊆ D`、塔 `Λ`（(2.1)）について、`Λ` と両立する
作用をもつ `D` 代数 `C_D` があり、係数制限で `𝔡` の冪で消える `C_D` 加群の上に加法的で非負な長さ
`λ_D = λ_∞` が定まり、`D` の任意のパラメータ系 `z` と `v ≥ 1` で

- (2.4) `λ_D H_i(z^v; C_D) = 0`（`i > 0`）、
- (2.5) `λ_D(C_D/(z^v)C_D) = v^h e((z), D)`（正で有限）、
- (2.6) `λ_D(C_D/(t^v)C_D) = v^h rank_A D`（`A` の正則パラメータ `t`）。

標数 `p` では `C_D = D_perf`、Monsky の定理（Hilbert–Kunz 重複度の存在）、Roberts の Frobenius
ホモロジー定理、Koszul Euler 標数の公式による。混標数では `C_D = (D ⊗_A A_∞)_perfd`
（Bhatt–Scholze）と CLMST の Cor. 4.0.4、Prop. 4.0.10、4.0.14 による。深い定理なので主張だけ置く
（`sorry`）。証明の形式化は `notes/section-2-plan.md` 段階 E。

## 主張の形

- **塔の作用との両立**：`C` は `A` 代数・`D` 代数・`Λ = Tower A t p` 代数で、`D` と `Λ` の構造は
  どちらも `A` 上で両立する（`IsScalarTower A D C`、`IsScalarTower A Λ C`）。`C` は可換なので `Λ` と `D` の作用は
  自動的に可換。
- **`λ_D = λ_∞`**：`λ_D` は `λ_∞`（`towerLength`）の `Λ → C` に沿った係数制限として**定義**する
  （`towerLengthOn`）。加法性の定義域は `𝔡 C` 冪ねじれ加群で、これは `Λ` 加群として `m_A Λ` 冪
  ねじれ（`m_A C ≤ 𝔡 C`）。論文の「Lemma 2.3 の有限段・下限・上限の性質は塔の加群の上で使える」は
  定義から従う（Lemma 5.4 はこの形で使う）。
- **(2.5)** の `e((z), D)` は `CommutativeAlgebra/HilbertSamuel.lean` の Hilbert–Samuel 重複度
  （Samuel 関数の多項式の最高次係数）。「正で有限」は `HilbertSamuel.multiplicity_pos` から出るので
  結論には入れない。
- `Λ` は具体的に定義した塔（`Paper/Section2/Tower.lean`）、`λ_∞` は具体的に定義した正規化長さ
  （`TowerLength.lean`）なので、どちらも仮定ではない。
-/

@[expose] public section

universe u

open IsLocalRing
open scoped ENNReal

namespace SerrePositivity

namespace Section2

/-- 局所環 `A` 上有限な局所環 `D` で `A → D` が単射なら `m_A D ⊆ m_D`（`A → D` は整拡大なので
局所準同型）。 -/
lemma maximalIdeal_map_le_of_finite_of_injective (A D : Type u) [CommRing A] [IsLocalRing A]
    [CommRing D] [IsLocalRing D] [Algebra A D] [Module.Finite A D]
    (hinj : Function.Injective (algebraMap A D)) :
    (maximalIdeal A).map (algebraMap A D) ≤ maximalIdeal D := by
  have : FaithfulSMul A D := (faithfulSMul_iff_algebraMap_injective A D).mpr hinj
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  exact (mem_nonunits_iff.mp ((mem_maximalIdeal a).mp ha)) (IsLocalHom.map_nonunit a hu)

variable (A D : Type u) [CommRing A] [IsLocalRing A] [CommRing D] [IsLocalRing D] [Algebra A D]
  [Module.Finite A D] (hinj : Function.Injective (algebraMap A D)) {h : ℕ} (t : Fin h → A) (p : ℕ)
  (C : Type u) [CommRing C] [Algebra A C] [Algebra D C] [Algebra (Tower A t p) C]
  [IsScalarTower A D C] [IsScalarTower A (Tower A t p) C]

include hinj in
/-- `m_A C ≤ 𝔡 C`：`m_A Λ` の `C` での像は `m_D C` に入る。 -/
lemma towerMaxIdeal_map_le :
    (towerMaxIdeal A t p).map (algebraMap (Tower A t p) C) ≤
      (maximalIdeal D).map (algebraMap D C) := by
  dsimp only [towerMaxIdeal]
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq A D C,
    ← Ideal.map_map]
  exact Ideal.map_mono (maximalIdeal_map_le_of_finite_of_injective A D hinj)

/-- **`λ_D`**：`λ_∞` の `Λ → C` に沿った係数制限。`𝔡 C` 冪ねじれ `C` 加群の上の正規化長さ。 -/
noncomputable def towerLengthOn : NormalizedLength C ((maximalIdeal D).map (algebraMap D C)) :=
  (towerLength A t p).comap (algebraMap (Tower A t p) C) _ (towerMaxIdeal_map_le A D hinj t p C)

/-- `λ_D(M)` は `M` を `Λ` 加群とみた `λ_∞(M)`。 -/
lemma towerLengthOn_len (M : Type u) [AddCommGroup M] [Module C M] :
    (towerLengthOn A D hinj t p C).len M =
      (letI := Module.compHom M (algebraMap (Tower A t p) C); towerLengthFun A t p M) := rfl

/-- **Theorem 2.5**（正規化長さの入力、`sorry`：Monsky、Roberts、CLMST、Bhatt–Scholze）。 -/
theorem theorem_2_5 (A D : Type u) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [IsDomain D]
    [IsAdicComplete (maximalIdeal D) D] [Algebra A D] [Module.Finite A D]
    [Algebra.IsSeparable A D]
    (hinj : Function.Injective (algebraMap A D))
    (hres : Function.Surjective ((residue D).comp (algebraMap A D)))
    {h : ℕ} (t : Fin h → A) (hdimA : ringKrullDim A = h) (hdimD : ringKrullDim D = h)
    (hpos : 0 < h) (ht : Ideal.span (Set.range t) = maximalIdeal A)
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t))
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField D) p] [PerfectField (ResidueField D)] :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra D C)
      (_ : Algebra (Tower A t p) C) (_ : IsScalarTower A D C)
      (_ : IsScalarTower A (Tower A t p) C),
      -- (2.4)
      (∀ (z : Fin h → D), IsSystemOfParameters D z → ∀ v : ℕ, 0 < v → ∀ i : ℕ, 0 < i →
        (towerLengthOn A D hinj t p C).len
          (koszulHomologySelf (fun j ↦ algebraMap D C (z j ^ v)) i) = 0) ∧
      -- (2.5)
      (∀ (z : Fin h → D), IsSystemOfParameters D z → ∀ v : ℕ, 0 < v →
        (towerLengthOn A D hinj t p C).len
          (C ⧸ Ideal.span (Set.range fun j ↦ algebraMap D C (z j ^ v))) =
          ENNReal.ofReal ((v : ℝ) ^ h *
            (HilbertSamuel.multiplicity D (Ideal.span (Set.range z)) D : ℝ))) ∧
      -- (2.6)
      (∀ v : ℕ, 0 < v →
        (towerLengthOn A D hinj t p C).len
          (C ⧸ Ideal.span (Set.range fun j ↦ algebraMap D C (algebraMap A D (t j) ^ v))) =
          ((v ^ h * Module.finrank A D : ℕ) : ℝ≥0∞)) := by
  sorry

end Section2

end SerrePositivity
