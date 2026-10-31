module

public import SerrePositivity.CommutativeAlgebra.HilbertSamuel
public import SerrePositivity.CommutativeAlgebra.Koszul
public import SerrePositivity.Paper.Section2.TowerLength
public import SerrePositivity.CommutativeAlgebra.RootTower.Completion
public import SerrePositivity.LengthAlgebra.Normalized
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
加法性は共通層で証明した塔の正規化長さから従う。
-/

@[expose] public section

universe u

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
