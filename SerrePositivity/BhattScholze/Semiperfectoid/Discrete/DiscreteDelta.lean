module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Delta.Basic.DeltaRing
public import Mathlib.Algebra.Regular.Defs

/-!
# 離散な環の δ 構造

## 概要
Frobenius の持ち上げや包絡との環同型から、基底に両立する δ 構造を得る。

## 方針
p 正則な終域での Frobenius の一意性と、環同型による Witt 切断の移送を使う。

## 規約
BS 著者版 Lemma 7.7 (1) の古典環の場合。

## 使われ方
離散な環から prism を組み立てる際の δ 構造。
-/

public noncomputable section

universe u v w

namespace SerrePositivity.BhattScholze.DeltaStructure

variable {p : ℕ} [Fact p.Prime]
variable {A : Type u} [CommRing A] {C : Type v} [CommRing C]

/-- 概要：p 正則な環の Frobenius 持ち上げから、指定の基底射を保つ一意な δ 構造を得る。
方針：Frobenius を持ち上げる δ 構造の一意性と、終域での p 倍の消去を使う。
規約：BS 著者版 Lemma 7.7 (1) の p 正則な場合。
使われ方：離散な環への δ 構造の付与。 -/
theorem existsUnique_over_of_frobeniusLift (D₀ : DeltaStructure p A) (η : A →+* C)
    (hp : IsRegular (p : C)) (φ : C →+* C)
    (hφ : ∀ x, (p : C) ∣ φ x - x ^ p)
    (hη : φ.comp η = η.comp D₀.frobeniusLift) :
    ∃! D : DeltaStructure p C, D.frobeniusLift = φ ∧ D₀.IsDeltaHom D η := by
  obtain ⟨D, hD, hu⟩ := existsUnique_of_frobeniusLift hp.left φ hφ
  refine ⟨D, ⟨hD, isDeltaHom_of_map_frobeniusLift η hp.left ?_⟩, fun E hE ↦ hu E hE.1⟩
  intro x
  rw [hD]
  exact (RingHom.congr_fun hη x).symm

/-- 概要：Frobenius と基底脚を保つ環同型に沿って δ 構造を一意に引き戻す。
方針：Witt 切断を共役し、同型の単射性で Frobenius と基底の両立性を確かめる。
規約：BS 著者版 Lemma 7.7 (1) の包絡と同型な場合。
使われ方：既知の δ 構造を通常の環模型へ移す。 -/
theorem existsUnique_over_of_equiv {B : Type w} [CommRing B]
    (D₀ : DeltaStructure p A) (E : DeltaStructure p B)
    (η : A →+* C) (β : A →+* B) (hβ : D₀.IsDeltaHom E β)
    (e : C ≃+* B) (φ : C →+* C)
    (he : e.toRingHom.comp η = β)
    (hφ : e.toRingHom.comp φ = E.frobeniusLift.comp e.toRingHom) :
    ∃! D : DeltaStructure p C, D.IsDeltaHom E e.toRingHom ∧
      D.frobeniusLift = φ ∧ D₀.IsDeltaHom D η := by
  let D := E.comapEquiv e
  have hD : D.IsDeltaHom E e.toRingHom := E.comapEquiv_isDeltaHom e
  refine ⟨D, ⟨hD, ?_, ?_⟩, ?_⟩
  · apply RingHom.ext
    intro x
    apply e.injective
    exact (hD.map_frobeniusLift x).trans (RingHom.congr_fun hφ x).symm
  · intro x
    apply e.injective
    change (e.toRingHom.comp η) (D₀.delta x) = e (D.delta (η x))
    rw [he]
    exact (hβ x).trans
      ((congrArg E.delta (RingHom.congr_fun he x)).symm.trans (hD (η x)).symm)
  · intro D' hD'
    apply DeltaStructure.ext
    intro x
    apply e.injective
    exact (hD'.1 x).trans (hD x).symm

end SerrePositivity.BhattScholze.DeltaStructure

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Lemma 7.7" (partial := component) "BS-W15 K5（11-11）：離散な場合の δ 構造の一意性、離散な prism と Frobenius からの射、p 正則な部分圏での始性は本体。導来 prismatic コホモロジー Δ_R/A との同一視（G10、∞ 側）は drafts の A3/DiscreteCase"] _root_.SerrePositivity.BhattScholze.DeltaStructure.existsUnique_over_of_equiv
attribute [cite BS19 "Lemma 7.7" (partial := component) "BS-W15 K5（11-11）：離散な場合の δ 構造の一意性、離散な prism と Frobenius からの射、p 正則な部分圏での始性は本体。導来 prismatic コホモロジー Δ_R/A との同一視（G10、∞ 側）は drafts の A3/DiscreteCase"] _root_.SerrePositivity.BhattScholze.DeltaStructure.existsUnique_over_of_frobeniusLift
