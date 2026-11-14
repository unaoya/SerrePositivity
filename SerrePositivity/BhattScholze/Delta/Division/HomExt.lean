module

public import SerrePositivity.BhattScholze.Delta.DividedPower.PDivision.PDivisionCompletion

/-!
# 古典的な完備 p 除算環からの δ 射の一意性

## 概要
p 正則で p 完備な標的への δ 射は、除算を加える前の環で比較できる。

## 方針
除算変数の関係式から標的での可除性を得て、既存の一意延長を適用する。

## 規約
始域と変数と標的は独立の宇宙を許す。

## 使われ方
BS 著者版 Theorems 5.2・6.4 の結晶模型への評価と余単体射の可換性。
-/

public noncomputable section

universe u v w

namespace SerrePositivity.BhattScholze

variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] {S : Type v}
variable {T : Type w} [CommRing T]
variable (D : DeltaStructure p R) (E : DeltaStructure p T) (a : S → R)
variable (hreg : Function.Injective (fun x : T => (p : T) * x))
variable [IsAdicComplete (Ideal.span {(p : T)}) T]

local notation "C" => ClassicalDeltaDivisionCompletion D (p : R) a
local notation "U" => classicalDeltaDivisionMap D (p : R) a

include hreg

/-- 完備 p 除算環から p 正則な完備環への二つの δ 射は、標準脚で比較できる。 -/
theorem classicalPDivisionHom_ext (f g : C →+* T)
    (hf : (classicalDeltaDivisionStructure D (p : R) a).IsDeltaHom E f)
    (hg : (classicalDeltaDivisionStructure D (p : R) a).IsDeltaHom E g)
    (h : f.comp U = g.comp U) : f = g := by
  let φ := g.comp U
  have hφ : D.IsDeltaHom E φ := hg.comp (classicalDeltaDivisionMap_isDeltaHom D (p : R) a)
  have hp : φ (p : R) = (p : T) := map_natCast φ p
  have hd : Function.Injective (fun x : T => φ (p : R) * x) := by
    rw [hp]
    exact hreg
  have hdiv (s : S) : φ (p : R) ∣ φ (a s) := by
    rw [hp]
    refine ⟨g (classicalPDivisionVariable D a s), ?_⟩
    simpa only [φ, RingHom.comp_apply, map_mul, map_natCast] using
      (congrArg g (classicalPDivisionVariable_relation D a s)).symm
  exact (existsUnique_classicalDeltaDivisionHom D E (p : R) a φ hφ hd hdiv
    (Ideal.span {(p : T)}) (Ideal.subset_span rfl)
      (by rw [hp]; exact Ideal.subset_span rfl)).unique ⟨hf, h⟩ ⟨hg, rfl⟩

end SerrePositivity.BhattScholze
