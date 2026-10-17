module

public import Mathlib.SetTheory.Cardinal.Regular
public import SerrePositivity.BhattScholze.Andre.Transfinite.PerfectoidLimitCompleteness
public import SerrePositivity.BhattScholze.Andre.Transfinite.RootClosure

/-! # Type u 内の ω₁ と終段の完備性・根の存在

BS Thm 7.14（著者版 p.61）の超限反復のため、ω₁ 未満の段を
`Ordinal.ToType` で同じ宇宙に表し、可算データの上界を実証明する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre.Transfinite
open Ordinal Cardinal

/-- ## 概要
ω₁ 未満の順序数の Type u 表現は空でない。BS Thm 7.14（著者版 p.61）の塔の添字。

## 方針
正の順序数の ToType が空でないことを使う。

## 規約
Ordinal 自体の宇宙を塔の添字に持ち込まず、Ordinal.ToType を使う。

## 使われ方
同じ宇宙で有向余極限を構成する際の非空性を与える。
-/
instance omegaOneIndex_nonempty : Nonempty (Ordinal.ToType (ω₁ : Ordinal.{u})) :=
  Ordinal.nonempty_toType_iff.mpr (Ordinal.omega_pos 1).ne'

/-- ## 概要
ω₁ 未満の段には最大段がない。BS Thm 7.14（著者版 p.61）の後続段の存在を表す。

## 方針
ω₁ が極限順序数であることを ToType の順序へ移す。

## 規約
ToType の標準 SuccOrder を使い、別の後続写像は定義しない。

## 使われ方
各段の多項式の根を必ず真に後の段に添加する。
-/
instance omegaOneIndex_noMaxOrder : NoMaxOrder (Ordinal.ToType (ω₁ : Ordinal.{u})) := by
  apply Ordinal.isSuccPrelimit_type_lt_iff.mp
  rw [Ordinal.type_toType]
  exact (Cardinal.isSuccLimit_omega 1).isSuccPrelimit

/-- ## 概要
Type u に表した ω₁ 未満の段の任意の可算集合には上界がある。
BS Thm 7.14（著者版 p.61）の終段で、可算データを一段へ降ろす根拠となる。

## 方針
各段を ω₁ 未満の順序数に戻し、可算上限も ω₁ 未満であることを使う。

## 規約
上界も Ordinal.ToType ω₁ の元として与え、宇宙を増やさない。

## 使われ方
終段の自動的な p 進完備性を、上界条件なしの ω₁ 特化版として供給する。
-/
theorem omegaOneIndex_countable_upperBound
    (s : Set (Ordinal.ToType (ω₁ : Ordinal.{u}))) (hs : s.Countable) :
    ∃ j, ∀ i ∈ s, i ≤ j := by
  classical
  let g : s → Ordinal.{u} := fun i ↦ (Ordinal.ToType.toOrd i.val).val
  have hb : (⨆ i, g i) < (ω₁ : Ordinal.{u}) := by
    let := hs.to_subtype
    exact Ordinal.iSup_lt_omega_one (fun i ↦ (Ordinal.ToType.toOrd i.val).property)
  refine ⟨Ordinal.ToType.mk ⟨⨆ i, g i, hb⟩, ?_⟩
  intro i hi
  calc
    i = Ordinal.ToType.mk (Ordinal.ToType.toOrd i) := (Ordinal.ToType.mk.apply_symm_apply i).symm
    _ ≤ Ordinal.ToType.mk ⟨⨆ i, g i, hb⟩ := by
      apply Ordinal.ToType.mk.monotone
      change g ⟨i, hi⟩ ≤ iSup g
      exact le_ciSup (f := g) Ordinal.bddAbove_of_small ⟨i, hi⟩

/-- ## 概要
ω₁ 添字の p 完全忠実平坦な perfectoid 塔で各後続段が前段の正次数モニックの根を持てば、
終段は p 進完備かつ絶対整閉。BS Thm 7.14（著者版 p.61）の終段の二つの性質。

## 方針
ω₁ の可算集合の上界を完備性定理に適用し、多項式は有限係数の降下と後続段の根から処理する。

## 規約
環と添字は Type u。塔は実際の環・遷移写像・DirectedSystem として与える。
終段の perfectoid 性・完全忠実平坦性や塔の存在は結論しない。

## 使われ方
極限段の保存定理と超限再帰で塔を構成した後、終段の完備性と絶対整閉性を同時に供給する。
-/
theorem omegaOne_directLimit_complete_and_absolutelyIntegrallyClosed
    (R : Ordinal.ToType (ω₁ : Ordinal.{u}) → Type u) [∀ i, CommRing (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j)
    [DirectedSystem R (fun i j h ↦ f i j h)]
    (p : ℕ) [Fact p.Prime]
    (hR : ∀ i, IsIntegralPerfectoid (R i) p)
    (hflat : ∀ i j h, letI := (f i j h).toAlgebra;
      IsCompletelyFaithfullyFlat (Ideal.span {(p : R i)}) (R j))
    (hroot : ∀ i (P : Polynomial (R i)), P.Monic → 0 < P.natDegree →
      ∃ x : R (Order.succ i), P.eval₂ (f i (Order.succ i) (Order.le_succ i)) x = 0) :
    IsAdicComplete (Ideal.span {(p : Ring.DirectLimit R (fun i j h ↦ f i j h))})
      (Ring.DirectLimit R (fun i j h ↦ f i j h)) ∧
    IsAbsolutelyIntegrallyClosed (Ring.DirectLimit R (fun i j h ↦ f i j h)) := by
  refine ⟨isAdicComplete_directLimit_of_perfectoid_completelyFaithfullyFlat
    R f p hR hflat omegaOneIndex_countable_upperBound, ?_⟩
  apply isAbsolutelyIntegrallyClosed_directLimit_of_eventual_roots
  intro i P hP hdeg
  obtain ⟨x, hx⟩ := hroot i P hP hdeg
  exact ⟨Order.succ i, Order.le_succ i, x, hx⟩

end SerrePositivity.BhattScholze.Andre.Transfinite
