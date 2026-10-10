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
# 塔の正規化長さの係数制限

有限な局所環の包含 `A → D` と、`D` および塔 `Λ` の両立する作用を持つ代数 `C` について、
`λ_D` を `λ_∞` の係数制限として定義する。
`m_A C ≤ m_D C` により、定義域の冪ねじれ条件も移る。
代数 `C` の存在や定理2.5のホモロジー・重複度公式は、このファイルでは仮定しない。
加法性は `TowerLength` の名前付き未証明入力に依存する。
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

end Section2

end SerrePositivity
