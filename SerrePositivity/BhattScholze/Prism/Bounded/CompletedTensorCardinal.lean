module

public import SerrePositivity.BhattScholze.Prism.Bounded.CompletedTensor
import SerrePositivity.BhattScholze.Prism.Bounded.CompletionFiniteResidue
import Mathlib.SetTheory.Cardinal.Free

/-!
# 完備テンソル積の濃度

## 概要
古典的に完備なテンソル積は、許容する濃度上限に収まる。

## 方針
通常のテンソル積の濃度を生成する純テンソルで評価し、有限剰余の可算直積で完備化を評価する。

## 規約
BS 著者版 Corollary 3.12 (a) の、切り落としを持つ site における濃度条件。

## 使われ方
平坦な押し出しを切り落としの中に構成する。
-/

public noncomputable section

universe u

namespace SerrePositivity.BhattScholze

open DerivedCompletion
open scoped Cardinal TensorProduct

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]

private theorem tensorProduct_mk_le {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ)
    (hB : Cardinal.mk B ≤ κ) (hC : Cardinal.mk C ≤ κ) :
    Cardinal.mk (B ⊗[A] C) ≤ κ := by
  let f : FreeAbelianGroup (B × C) →+ B ⊗[A] C :=
    FreeAbelianGroup.lift (fun x ↦ x.1 ⊗ₜ[A] x.2)
  have hf : Function.Surjective f := by
    intro x
    refine TensorProduct.inductionOn (motive := fun y ↦ ∃ z, f z = y) x
      (fun b c ↦ ⟨FreeAbelianGroup.of (b, c), FreeAbelianGroup.lift_apply_of _ _⟩) ?_
    intro x y hx hy
    obtain ⟨z, hz⟩ := hx
    obtain ⟨w, hw⟩ := hy
    exact ⟨z + w, by rw [map_add, hz, hw]⟩
  refine (Cardinal.mk_le_of_surjective hf).trans ?_
  rw [Cardinal.mk_freeAbelianGroup]
  refine max_le ?_ hκ
  rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id, ← Cardinal.mul_eq_self hκ]
  exact mul_le_mul' hB hC

set_option maxHeartbeats 800000 in
/-- 概要：古典的に完備なテンソル積の濃度は、両因子の許容上限以下。
方針：有限剰余は生のテンソル積の剰余と同型なので、可算直積で評価する。
規約：κ は無限で κ^ℵ₀ = κ。完備性は基底の二座標について。
使われ方：有界 prism の押し出しの濃度。 -/
theorem prismCompletedTensor_mk_le {p : ℕ} [Fact p.Prime] (Q : OrientedPrism p B)
    {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) (hk : κ ^ ℵ₀ = κ)
    (hB : Cardinal.mk B ≤ κ) (hC : Cardinal.mk C ≤ κ)
    (hc : let H := PrismCompletedTensor (A := A) (C := C) Q
      IsAdicComplete (Ideal.span {(p : H), prismCompletedTensorLeft Q Q.generator}) H) :
    Cardinal.mk (PrismCompletedTensor (A := A) (C := C) Q) ≤ κ := by
  let T := B ⊗[A] C
  let d : T := Algebra.TensorProduct.includeLeftRingHom Q.generator
  let H := PrismCompletedTensor (A := A) (C := C) Q
  let u := pdCompletionUnit T p d
  let I := Ideal.span {(p : T), d}
  have hmap : I.map u = Ideal.span {(p : H), prismCompletedTensorLeft Q Q.generator} := by
    rw [Ideal.map_span, Set.image_pair, map_natCast]
    rfl
  let J := I.map u
  let : IsAdicComplete J H := by
    change IsAdicComplete (I.map u) H
    rw [hmap]
    exact hc
  have hT : Cardinal.mk T ≤ κ := tensorProduct_mk_le (A := A) hκ hB hC
  have hpI : (p : T) ∈ I := Ideal.subset_span (Set.mem_insert (p : T) {d})
  have hdI : d ∈ I :=
    Ideal.subset_span (Set.mem_insert_of_mem (p : T) (Set.mem_singleton d))
  have hq (n : ℕ) : Cardinal.mk (H ⧸ (J ^ n • ⊤ : Submodule H H)) ≤ κ := by
    obtain ⟨e, _⟩ := exists_pdCompletion_finiteResidue_equiv p d (I ^ n) n n
      (Ideal.pow_mem_pow hpI n) (Ideal.pow_mem_pow hdI n)
    have hj : (J ^ n • ⊤ : Submodule H H) = (I ^ n).map u := by
      change ((I.map u) ^ n * ⊤ : Ideal H) = (I ^ n).map u
      rw [Ideal.mul_top, Ideal.map_pow]
    let eq := Submodule.quotEquivOfEq (J ^ n • ⊤ : Submodule H H)
      ((I ^ n).map u : Submodule H H) hj
    exact (Cardinal.mk_congr (eq.toEquiv.trans e.toEquiv)).le.trans
      ((Cardinal.mk_le_of_surjective (Ideal.Quotient.mk_surjective (I := I ^ n))).trans hT)
  have hH : Cardinal.mk H ≤ Cardinal.mk (AdicCompletion J H) :=
    Cardinal.mk_le_of_injective (AdicCompletion.of_injective (I := J) (M := H))
  have hA : Cardinal.mk (AdicCompletion J H) ≤
      Cardinal.mk (∀ n : ℕ, H ⧸ (J ^ n • ⊤ : Submodule H H)) :=
    Cardinal.mk_le_of_injective Subtype.val_injective
  refine hH.trans (hA.trans ?_)
  rw [Cardinal.mk_pi]
  calc
    _ ≤ Cardinal.prod (fun _ : ℕ ↦ κ) := Cardinal.prod_le_prod _ _ hq
    _ = κ := by rw [Cardinal.prod_const, Cardinal.lift_uzero, Cardinal.mk_nat,
      Cardinal.lift_aleph0, hk]

end SerrePositivity.BhattScholze
