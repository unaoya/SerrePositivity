module

public import SerrePositivity.BhattScholze.Andre.Transfinite.CompletedMaps
public import SerrePositivity.BhattScholze.Andre.Transfinite.PerfectoidCompletionColimit
public import SerrePositivity.BhattScholze.Andre.Transfinite.OmegaOne

/-! # ω₁ 塔の終段における三性質

BS Thm 7.14（著者版 p.61）の超限塔が与えられた後の合成を行う。
塔の存在を追加の公理や引用として宣言しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre.Transfinite
open Ordinal Cardinal
/-- ## 概要
ω₁ の小さい添字型に最小元を与える。BS Thm 7.14（著者版 p.61）の初段に用いる。

## 方針
非空な整列線形順序の標準の最小元構造を使う。

## 規約
添字は Ordinal.ToType ω₁ のままで、Type u に留まる。

## 使われ方
最小段から終段への標準環準同型を指定する。
-/
instance omegaOneIndex_orderBot : OrderBot (Ordinal.ToType (ω₁ : Ordinal.{u})) :=
  WellFoundedLT.toOrderBot _

/-- ## 概要
ω₁ 添字の p 完全忠実平坦な perfectoid 塔で、各後続段が前段の全正次数モニック多項式の
根を持てば、環余極限は perfectoid かつ絶対整閉であり、初段からの標準射は p 完全忠実平坦。
BS Thm 7.14（著者版 p.61）の終段の三性質を合成する。

## 方針
可算添字集合の上界から完備性と perfectoid 性を得る。最小段からの完全忠実平坦性は
通常の有向余極限で保存する。多項式の有限係数を一段に降ろし、次段で根を取る。

## 規約
環と添字は Type u。塔は実際の環・遷移射・DirectedSystem として引数に与える。
塔自体の存在や一段拡大を新たな仮定なしで証明したことにはしない。

## 使われ方
訂正済み step による超限塔を構成した後、Thm 7.14 の結論を取り出す。
-/
theorem omegaOne_directLimit_properties
    (R : Ordinal.ToType (ω₁ : Ordinal.{u}) → Type u) [∀ i, CommRing (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j)
    [DirectedSystem R (fun i j h ↦ f i j h)]
    (p : ℕ) [Fact p.Prime]
    (hR : ∀ i, IsIntegralPerfectoid (R i) p)
    (hflat : ∀ i j h, let := (f i j h).toAlgebra;
      IsCompletelyFaithfullyFlat (Ideal.span {(p : R i)}) (R j))
    (hroot : ∀ i (P : Polynomial (R i)), P.Monic → 0 < P.natDegree →
      ∃ x : R (Order.succ i), P.eval₂ (f i (Order.succ i) (Order.le_succ i)) x = 0) :
    let L := Ring.DirectLimit R (fun i j h ↦ f i j h)
    IsIntegralPerfectoid L p ∧
      (let := (Ring.DirectLimit.of R (fun i j h ↦ f i j h) ⊥).toAlgebra
       IsCompletelyFaithfullyFlat (Ideal.span {(p : R ⊥)}) L) ∧
      IsAbsolutelyIntegrallyClosed L := by
  refine ⟨isIntegralPerfectoid_ringDirectLimit_of_countable_upperBound
    R f hR hflat omegaOneIndex_countable_upperBound, ?_, ?_⟩
  · exact isCompletelyFaithfullyFlat_ringDirectLimit_of_orderBot R f (fun i ↦ hflat ⊥ i bot_le)
  · exact (omegaOne_directLimit_complete_and_absolutelyIntegrallyClosed R f p hR hflat hroot).2
end SerrePositivity.BhattScholze.Andre.Transfinite
