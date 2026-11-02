module

public import SerrePositivity.LengthAlgebra.RootTowerLength.Basic
public import SerrePositivity.LengthAlgebra.RootTowerLength.Additivity
public import SerrePositivity.LengthAlgebra.Normalized
public import SerrePositivity.CommutativeAlgebra.HilbertSamuel
public import SerrePositivity.CommutativeAlgebra.Koszul.Basic
public import SerrePositivity.CommutativeAlgebra.RootTower.Completion
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import SerrePositivity.HomologicalAlgebra.FlatBaseChange
public import SerrePositivity.LengthAlgebra.RootTowerLength.Completion
public import SerrePositivity.CommutativeAlgebra.RootTower.Koszul

/-! # 根の塔の正規化長さ

## 概要

根の塔 `Λ` 上の正規化長さ `towerLength` を共通層の `NormalizedLength` として与え、有限生成一致 C1 と加法性 C2、有限段の λ* の公式を使う二つの有限段公式を示す。有限な局所環の包含 `A → D` と両立する作用を持つ代数 `C` について、`λ_D` を `λ_∞` の係数制限 `towerLengthOn` として定める。`B = Λ ⊗_{A_n} T` の Koszul ホモロジーの正規化長さを有限段の長さ `/p^(nh)` で表し、根の塔の完備化の上の長さの係数制限を比べる。

## 方針

数値関数とその零・同型不変性、有限表示の降下と λ* の有限段公式は `RootTowerLength/Basic` にある。

## 規約

代数 `C` の存在や定理 2.5 のホモロジー・重複度公式はここでは仮定しない。

## 使われ方

Paper/Section2（Theorem 2.5）、`BaseChangeApproximation`、CLMST/Inputs。
-/

@[expose] public noncomputable section

universe u

section TowerLengthPart

open IsLocalRing TensorProduct
open scoped ENNReal

namespace SerrePositivity
namespace Section2

variable (A : Type u) [CommRing A] {h : ℕ} (t : Fin h → A) (p : ℕ)

/-! ## Lemma 2.3 (b)：証明した性質と標準事実

**証明済みの有限生成一致と加法性**

- (C1) `towerLengthFun_eq_fgLength`：有限生成で `m_A` 冪ねじれの加群で `λ_∞ = λ*`。
  CLMST（Cai–Lee–Ma–Schwede–Tucker, arXiv:2209.04046v4）Proposition 2.2.3 の主張
  「`λ_∞` は well defined で、有限生成加群では `λ_∞^*` と一致する」。その証明は
  Gabber–Ramero, *Foundations for almost ring theory*, Lemma 14.5.74（または Shimomoto, Lemma 2.2）
  に関連する。ここでは標準基底より弱い Noether 局所環の条件で証明した。
  内容は「有限生成 `N` の有限生成部分加群 `N'` について `λ*(N') ≤ λ*(N)`」
  （`λ*` の単調性）で、これが (2.3) の上限が `λ*` 自身に戻ることを保証する。
- (C2) `towerLengthFun_add_of_exact`：`m_A` 冪ねじれ加群の短完全列での加法性。
  CLMST Proposition 2.2.6(a) に対応する性質を、有限段の長さ・有限表示な被覆・
  有限生成部分による近似で証明した。文献の加法性の引用には依存しない。

**証明済みの標準事実（このファイルの `TowerDescentPart`）**

- (S1) `fgLength_tensor`：有限長 `A_n` 加群 `V` で `λ*(Λ ⊗_{A_n} V) = ℓ_{A_n}(V) / p^{nh}`。
- (S2) `exists_descent`：`m_A` 冪ねじれで有限表示な `Λ` 加群は、ある段の有限長 `A_n` 加群から
  `Λ ⊗_{A_n} V` として得られる。

(2.2) `towerLengthFun_tensor` は (C1) と (S1) から導く（同じファイル）。 -/

variable [IsLocalRing A]

set_option linter.unusedVariables false in
/-- (C1) **有限生成加群で `λ_∞ = λ*`**。有限段の長さで証明済み。
CLMST Prop. 2.2.3 の有限生成一致を、Noether 局所環の条件で導く。
冪ねじれの引数は既存利用との互換性のため残す。新しい数値関数の証明には不要。 -/
theorem towerLengthFun_eq_fgLength [IsNoetherianRing A] [Fact p.Prime]
    (ht : ∀ i, t i ∈ maximalIdeal A)
    (N : Type u) [AddCommGroup N] [Module (Tower A t p) N]
    [Module.Finite (Tower A t p) N] (hN : IsPowTorsion (towerMaxIdeal A t p) N) :
    towerLengthFun A t p N = fgLength A t p N := by
  clear hN
  exact towerLengthFun_eq_fgLength_of_noetherian A t p ht N

/-- (C2) **加法性**。有限段の長さと近似から証明済み。
`m_A Λ` 冪ねじれ加群の短完全列 `0 → M₁ → M₂ → M₃ → 0` で `λ_∞(M₂) = λ_∞(M₁) + λ_∞(M₃)`。 -/
theorem towerLengthFun_add_of_exact [IsNoetherianRing A] [Fact p.Prime]
    (ht : ∀ i, t i ∈ maximalIdeal A) (M₁ M₂ M₃ : Type u) [AddCommGroup M₁]
    [Module (Tower A t p) M₁] [AddCommGroup M₂] [Module (Tower A t p) M₂] [AddCommGroup M₃]
    [Module (Tower A t p) M₃] (f : M₁ →ₗ[Tower A t p] M₂) (g : M₂ →ₗ[Tower A t p] M₃)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (hM₂ : IsPowTorsion (towerMaxIdeal A t p) M₂) :
    towerLengthFun A t p M₂ = towerLengthFun A t p M₁ + towerLengthFun A t p M₃ := by
  exact towerLengthFun_add_of_exact_of_noetherian A t p ht f g hf hg hfg hM₂

/-! ## 正規化長さの構造 -/

/-- **`λ_∞`**：塔 `Λ` の、`m_A Λ` 冪ねじれ加群の上の正規化長さ。値は `towerLengthFun`、加法性は
共通層で証明済み。 -/
noncomputable def towerLength [IsNoetherianRing A] [Fact p.Prime]
    (ht : ∀ i, t i ∈ maximalIdeal A) :
    NormalizedLength (Tower A t p) (towerMaxIdeal A t p) :=
  RootTowerLength.normalizedLength A t p ht

@[simp] lemma towerLength_len [IsNoetherianRing A] [Fact p.Prime]
    (ht : ∀ i, t i ∈ maximalIdeal A)
    (M : Type u) [AddCommGroup M] [Module (Tower A t p) M] :
    (towerLength A t p ht).len M = towerLengthFun A t p M := rfl

/-- **上限の性質 (2.3)**：`λ_∞(M) = sup{λ_∞(N) : N ⊆ M 有限生成}`。定義（`λ*` の上限）と、
有限生成加群で `λ_∞ = λ*` であること（`towerLengthFun_eq_fgLength`）から。 -/
theorem towerLength_hasSup [IsNoetherianRing A] [Fact p.Prime]
    (ht : ∀ i, t i ∈ maximalIdeal A) : (towerLength A t p ht).HasSup :=
  RootTowerLength.normalizedLength_hasSup A t p ht

end Section2

end SerrePositivity

end TowerLengthPart

section TowerDescentPart

open IsLocalRing TensorProduct
open scoped ENNReal

namespace SerrePositivity
namespace Section2

variable (A : Type u) [CommRing A] {h : ℕ} (t : Fin h → A) (p : ℕ)

section formula2
variable [IsLocalRing A]

variable [IsNoetherianRing A] [Fact p.Prime] (ht : ∀ i, t i ∈ maximalIdeal A)

set_option linter.style.haveILetI false in
include ht in
/-- **(2.2) 有限段の公式**：`λ_∞(Λ ⊗_{A_n} V) = ℓ_{A_n}(V) / p^{nh}`。(C1) と (S1) から。 -/
theorem towerLengthFun_tensor (n : ℕ) (V : Type u) [AddCommGroup V]
    [Module (TowerStage A t p n) V] (hV : IsFiniteLength (TowerStage A t p n) V)
    (hVt : IsPowTorsion ((maximalIdeal A).map (algebraMap A (TowerStage A t p n))) V) :
    towerLengthFun A t p (Tower A t p ⊗[TowerStage A t p n] V) =
      (Module.length (TowerStage A t p n) V : ℝ≥0∞) / (stageRank h p n : ℝ≥0∞) := by
  haveI : IsNoetherian (TowerStage A t p n) V :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hV).1
  rw [towerLengthFun_eq_fgLength A t p ht _ (isPowTorsion_tower_tensor A t p n V hVt),
    fgLength_tensor A t p ht n V hV]

include ht in
/-- 有限長の段加群では、有限段の公式の冪ねじれ条件は自動的に満たされる。
極大イデアルのある冪が加群を消し、基底の極大イデアルの像はその極大イデアルに入る。 -/
theorem towerLengthFun_tensor_of_finiteLength (n : ℕ) (V : Type u) [AddCommGroup V]
    [Module (TowerStage A t p n) V] (hV : IsFiniteLength (TowerStage A t p n) V) :
    towerLengthFun A t p (Tower A t p ⊗[TowerStage A t p n] V) =
      (Module.length (TowerStage A t p n) V : ℝ≥0∞) / (stageRank h p n : ℝ≥0∞) := by
  let := isLocalRing_towerStage A t p ht n
  apply towerLengthFun_tensor A t p ht n V hV
  obtain ⟨k, hk⟩ := IsFiniteLength.exists_isTorsionBySet_maximalIdeal_pow hV
  refine ⟨k, ?_⟩
  rw [Module.isTorsionBySet_iff_subset_annihilator] at hk ⊢
  exact (pow_le_pow_left'
    (le_of_isMaximal_towerStage A t p ht n (maximalIdeal (TowerStage A t p n))).1 k).trans hk

end formula2

end Section2

end SerrePositivity

end TowerDescentPart

section TowerLengthOnPart

open IsLocalRing
open scoped ENNReal

namespace SerrePositivity

namespace Section2

variable (A D : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [CommRing D] [IsLocalRing D] [Algebra A D]
  [Module.Finite A D] (hinj : Function.Injective (algebraMap A D)) {h : ℕ} (t : Fin h → A) (p : ℕ)
  [Fact p.Prime] (ht : ∀ i, t i ∈ maximalIdeal A)
  (C : Type u) [CommRing C] [Algebra A C] [Algebra D C] [Algebra (Tower A t p) C]
  [IsScalarTower A D C] [IsScalarTower A (Tower A t p) C]

/-- **`λ_D`**：`λ_∞` の `Λ → C` に沿った係数制限。`𝔡 C` 冪ねじれ `C` 加群の上の正規化長さ。 -/
noncomputable def towerLengthOn : NormalizedLength C ((maximalIdeal D).map (algebraMap D C)) :=
  (towerLength A t p ht).comap (algebraMap (Tower A t p) C) _ (towerMaxIdeal_map_le A D hinj t p C)

/-- `λ_D(M)` は `M` を `Λ` 加群とみた `λ_∞(M)`。 -/
lemma towerLengthOn_len (M : Type u) [AddCommGroup M] [Module C M] :
    (towerLengthOn A D hinj t p ht C).len M =
      (letI := Module.compHom M (algebraMap (Tower A t p) C); towerLengthFun A t p M) := rfl

end Section2

end SerrePositivity

end TowerLengthOnPart

section TowerKoszulLengthPart

namespace SerrePositivity.Section2

open IsLocalRing
open scoped ENNReal

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (ht : ∀ j, t j ∈ maximalIdeal A) (n : ℕ)
    (T B : Type u) [CommRing T] [CommRing B]
    [Algebra (TowerStage A t p n) T] [Algebra (Tower A t p) B] [Algebra T B]
    [Algebra (TowerStage A t p n) B]
    [IsScalarTower (TowerStage A t p n) (Tower A t p) B]
    [IsScalarTower (TowerStage A t p n) T B]
    [Algebra.IsPushout (TowerStage A t p n) (Tower A t p) T B]

include ht in
/-- 有限段から係数拡大された Koszul ホモロジーの正規化長さの公式。 -/
theorem towerLengthFun_koszulHomology_of_baseChange {r : ℕ} (x : Fin r → T) (i : ℤ)
    (hfin :
      letI := Module.compHom ((koszulComplex x).homology i)
        (algebraMap (TowerStage A t p n) T)
      IsFiniteLength (TowerStage A t p n) ((koszulComplex x).homology i)) :
    letI := Module.compHom ((koszulComplex x).homology i)
      (algebraMap (TowerStage A t p n) T)
    letI := Module.compHom ((koszulComplex (algebraMap T B ∘ x)).homology i)
      (algebraMap (Tower A t p) B)
    towerLengthFun A t p ((koszulComplex (algebraMap T B ∘ x)).homology i) =
      (Module.length (TowerStage A t p n) ((koszulComplex x).homology i) : ℝ≥0∞) /
        (stageRank h p n : ℝ≥0∞) := by
  let : Module (TowerStage A t p n) ((koszulComplex x).homology i) :=
    Module.compHom _ (algebraMap (TowerStage A t p n) T)
  let : Module (Tower A t p) ((koszulComplex (algebraMap T B ∘ x)).homology i) :=
    Module.compHom _ (algebraMap (Tower A t p) B)
  let := flat_tower A t p n
  rw [towerLengthFun_congr
    (pushoutKoszulHomologyEquiv (TowerStage A t p n) (Tower A t p) T B x i)]
  exact towerLengthFun_tensor_of_finiteLength A t p ht n _ hfin

include ht in
omit [IsNoetherianRing A] in
/-- 同じ有限長性は、係数拡大後のホモロジーが `m_A Λ` の冪で消えることも与える。 -/
theorem isPowTorsion_koszulHomology_of_baseChange {r : ℕ} (x : Fin r → T) (i : ℤ)
    (hfin :
      letI := Module.compHom ((koszulComplex x).homology i)
        (algebraMap (TowerStage A t p n) T)
      IsFiniteLength (TowerStage A t p n) ((koszulComplex x).homology i)) :
    letI := Module.compHom ((koszulComplex (algebraMap T B ∘ x)).homology i)
      (algebraMap (Tower A t p) B)
    IsPowTorsion (towerMaxIdeal A t p)
      ((koszulComplex (algebraMap T B ∘ x)).homology i) := by
  let : Module (Tower A t p) ((koszulComplex (algebraMap T B ∘ x)).homology i) :=
    Module.compHom _ (algebraMap (Tower A t p) B)
  let := flat_tower A t p n
  let := isLocalRing_towerStage A t p ht n
  let M := (koszulComplex x).homology i
  let : Module (TowerStage A t p n) M :=
    Module.compHom M (algebraMap (TowerStage A t p n) T)
  apply IsPowTorsion.of_equiv
    (pushoutKoszulHomologyEquiv (TowerStage A t p n) (Tower A t p) T B x i).symm
  apply isPowTorsion_tower_tensor
  obtain ⟨k, hk⟩ := IsFiniteLength.exists_isTorsionBySet_maximalIdeal_pow hfin
  refine ⟨k, ?_⟩
  rw [Module.isTorsionBySet_iff_subset_annihilator] at hk ⊢
  exact (pow_le_pow_left'
    (le_of_isMaximal_towerStage A t p ht n (maximalIdeal (TowerStage A t p n))).1 k).trans hk

end SerrePositivity.Section2

end TowerKoszulLengthPart

section CompletedTowerPart

open IsLocalRing
namespace SerrePositivity.Section2

variable (A : Type u) [CommRing A] {h : ℕ} (t : Fin h → A) (p : ℕ)
    [IsLocalRing A] [IsNoetherianRing A] [Fact p.Prime] (ht : ∀ i, t i ∈ maximalIdeal A)

/-- 完備化上の正規化長さ：非完備な塔に制限して測る。 -/
noncomputable def completedTowerLength :
    NormalizedLength (CompletedTower A t p) (completedTowerMaxIdeal A t p) :=
  RootTowerLength.completedNormalizedLength A t p ht

variable (D : Type u) [CommRing D] [IsLocalRing D] [Algebra A D] [Module.Finite A D]
    (hinj : Function.Injective (algebraMap A D))
    (C : Type u) [CommRing C] [Algebra A C] [Algebra D C]
    [Algebra (Tower A t p) C] [Algebra (CompletedTower A t p) C]
    [IsScalarTower A D C] [IsScalarTower A (Tower A t p) C]
    [IsScalarTower A (CompletedTower A t p) C]
    [IsScalarTower (Tower A t p) (CompletedTower A t p) C]

omit [IsScalarTower A (CompletedTower A t p) C] in
/-- 完備化を経由して係数を制限しても、長さ代数の長さは変わらない。 -/
theorem towerLengthOn_eq_completedTowerLength
    (M : Type u) [AddCommGroup M] [Module C M] :
    (towerLengthOn A D hinj t p ht C).len M =
      (letI := Module.compHom M (algebraMap (CompletedTower A t p) C)
       (completedTowerLength A t p ht).len M) := by
  exact completedLengthOf_restrictScalars A t p (towerLength A t p ht) C M

end SerrePositivity.Section2

end CompletedTowerPart
