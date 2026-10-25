module

public import SerrePositivity.BhattScholze.Delta.DeltaDirectLimit
public import SerrePositivity.BhattScholze.Delta.PerfectDeltaFrobenius
/-! # 完全 δ 環の余極限の完全性

BS Lemma 3.9（著者版 pp.31–32）および Thm 7.14（p.61）の極限操作に用いる。
既存の任意図式の δ 余極限構造について、各段の Frobenius 同型を余極限へ移す。
-/

@[expose] public noncomputable section
open SerrePositivity.BhattScholze
universe u
namespace SerrePositivity.BhattScholze.Andre.Transfinite
variable {p : ℕ} [Fact p.Prime] {ι : Type u} [Preorder ι]
    (A : ι → Type u) [∀ i, CommRing (A i)]
    (f : ∀ i j, i ≤ j → A i →+* A j)
    (D : ∀ i, DeltaStructure p (A i))
    (hδ : ∀ i j h, (D i).IsDeltaHom (D j) (f i j h))
/-- ## 概要
完全 δ 環と δ 遷移射からなる図式の環余極限上の標準 δ 構造は完全である。
BS Lemma 3.9（著者版 pp.31–32）、Thm 7.14（p.61）の極限段に用いる補助命題。

## 方針
各段の Frobenius 環同型の両立性から余極限上の環同型を作り、
標準段射上でその同型が余極限の Frobenius 持上げそのものであることを示す。

## 規約
添字の有向性・非空性、遷移射の単射性、p 正則性を追加仮定としない。
既存の deltaDirectLimitStructure を使い、別の δ 構造は定義しない。

## 使われ方
perfectoid 塔の Fontaine 環の未完備余極限を完全 δ 環として扱う。
-/
theorem deltaDirectLimit_isPerfect (hD : ∀ i, (D i).IsPerfect) :
    (deltaDirectLimitStructure A (fun i j h ↦ f i j h) D (fun i j h x ↦ hδ i j h x)).IsPerfect := by
  let E := fun i ↦ (D i).frobeniusEquiv (hD i)
  have hc : ∀ i j h, (E j).toRingHom.comp (f i j h) = (f i j h).comp (E i) := by
    intro i j h
    ext x
    exact ((hδ i j h).map_frobeniusLift x).symm
  let e := Ring.DirectLimit.congr E hc
  have he : (deltaDirectLimitStructure A (fun i j h ↦ f i j h) D
      (fun i j h x ↦ hδ i j h x)).frobeniusLift = e.toRingHom := by
    apply Ring.DirectLimit.hom_ext
    intro i
    ext x
    change (deltaDirectLimitStructure A (fun i j h ↦ f i j h) D
      (fun i j h x ↦ hδ i j h x)).frobeniusLift (Ring.DirectLimit.of A (fun i j h ↦ f i j h) i x) =
      e (Ring.DirectLimit.of A (fun i j h ↦ f i j h) i x)
    rw [Ring.DirectLimit.congr_apply_of]
    exact ((deltaDirectLimitOf_isDeltaHom A (fun i j h ↦ f i j h) D
      (fun i j h x ↦ hδ i j h x) i).map_frobeniusLift x).symm
  change Function.Bijective _
  rw [he]
  exact e.bijective
end SerrePositivity.BhattScholze.Andre.Transfinite
