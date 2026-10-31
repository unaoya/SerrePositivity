module

public import SerrePositivity.CommutativeAlgebra.RootTower.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import SerrePositivity.CommutativeAlgebra.RootTower.Stage
public import SerrePositivity.CommutativeAlgebra.Adic.Completion.Tensor
public import SerrePositivity.CommutativeAlgebra.Adic.Completion.Algebra
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-! # 根の塔の p 進完備化と制限

## 概要

共通の根の塔の p 進完備化 `CompletedTower` と標準的な代数作用、拡大イデアルの比較を与える。塔が基底環上平坦なことから完備化上の正則元を移し、Noether 基底上では完備化した塔も基底上平坦なことを示す。有限で単射な局所環の写像で極大イデアルの像が包含されること（`maximalIdeal_map_le_of_finite_of_injective`）と、塔を経由する両立した作用での同じ包含も与える。

## 方針

完備化は Mathlib の `AdicCompletion` を使う。正則性の一般論は AdicCompletionRegular に置き、ここでは塔へ適用するだけにする。加群版と環版の完備化の比較で平坦性を移す。

## 規約

宣言は名前空間 `SerrePositivity.Section2` に置く（CLMST で `CompletedTower` が 754 箇所参照されるため変えない）。正規化長さ・perfectoid 性・Koszul ホモロジーは使わない。

## 使われ方

CLMST の完備化と長さの比較のほぼ全体、Paper/Section2/TowerLengthOn、LengthAlgebra/RootTowerLength。
-/

@[expose] public noncomputable section

universe u

section CompletionPart

open IsLocalRing
namespace SerrePositivity.Section2

variable (A : Type u) [CommRing A] {h : ℕ} (t : Fin h → A) (p : ℕ)

/-- 標準的な根の塔の `p` 進完備化。 -/
abbrev CompletedTower :=
  AdicCompletion (Ideal.span {(p : Tower A t p)}) (Tower A t p)

/-- 基底環と塔の作用は、完備化への標準写像と両立する。 -/
instance : IsScalarTower A (Tower A t p) (CompletedTower A t p) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

variable [IsLocalRing A]

/-- 完備化した塔における `m_A` の拡大。 -/
noncomputable def completedTowerMaxIdeal : Ideal (CompletedTower A t p) :=
  (maximalIdeal A).map (algebraMap A (CompletedTower A t p))

/-- 塔に拡大した極大イデアルを完備化へ移すと、直接の拡大と一致する。 -/
theorem towerMaxIdeal_map_completed :
    (towerMaxIdeal A t p).map (algebraMap (Tower A t p) (CompletedTower A t p)) =
      completedTowerMaxIdeal A t p := by
  simp only [towerMaxIdeal, completedTowerMaxIdeal, Ideal.map_map,
    ← IsScalarTower.algebraMap_eq]

end SerrePositivity.Section2

end CompletionPart

section CompletionFlatPart

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity

namespace Section2

variable (A : Type u) [CommRing A] {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]

/-- 未完備の根の塔は基底環上平坦。零段の有限自由性と塔の各段上の平坦性を合成する。 -/
theorem flat_tower_over_base : Module.Flat A (Tower A t p) := by
  let := towerStage_free A t p 0
  let := flat_tower A t p 0
  exact Module.Flat.trans A (TowerStage A t p 0) (Tower A t p)

/-- 基底環上で `p` が正則なら、完備化した根の塔上でも `p` は正則。
未完備の塔の平坦性と、主イデアル完備化上の正則性保存を用いる。 -/
theorem isSMulRegular_p_completedTower (hp : IsSMulRegular A (p : A)) :
    IsSMulRegular (CompletedTower A t p) (p : CompletedTower A t p) := by
  let := flat_tower_over_base A t p
  have ht : IsSMulRegular (Tower A t p) (p : Tower A t p) := by
    simpa using hp.of_flat (S := Tower A t p)
  simpa using isSMulRegular_adicCompletion_span_singleton (Tower A t p) (p : Tower A t p) ht

/-- Noether 基底上では、p 進完備化した根の塔も基底環上平坦。
未完備塔自身の Noether 性は要求しない。 -/
theorem flat_completedTower_over_base [IsNoetherianRing A] :
    Module.Flat A (CompletedTower A t p) := by
  let := flat_tower_over_base A t p
  have hf := flat_adicCompletion_algebra_of_flat (S := Tower A t p) (Ideal.span {(p : A)})
  have hI : (Ideal.span {(p : A)}).map (algebraMap A (Tower A t p)) =
      Ideal.span {(p : Tower A t p)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  rw [hI] at hf
  exact hf

/-- Noether基底では、完備塔は任意の有限段A_n上でも平坦。
有限段のNoether性と、未完備塔の各段上の平坦性を使う。 -/
theorem flat_completedTower_over_stage [IsNoetherianRing A] (n : ℕ) :
    Module.Flat (TowerStage A t p n) (CompletedTower A t p) := by
  let := towerStage_finite A t p n
  let : IsNoetherianRing (TowerStage A t p n) :=
    IsNoetherianRing.of_finite A (TowerStage A t p n)
  let := flat_tower A t p n
  have hf := flat_adicCompletion_algebra_of_flat (S := Tower A t p)
    (Ideal.span {(p : TowerStage A t p n)})
  have hI : (Ideal.span {(p : TowerStage A t p n)}).map
      (algebraMap (TowerStage A t p n) (Tower A t p)) = Ideal.span {(p : Tower A t p)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  rw [hI] at hf
  exact hf

end Section2
end SerrePositivity

end CompletionFlatPart

section RestrictionPart

open IsLocalRing
namespace SerrePositivity.Section2

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

end SerrePositivity.Section2

end RestrictionPart
