module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PDCompletionEquivalence
public import SerrePositivity.BhattScholze.Prism.Bounded.CompletedTensor

/-!
# 完備テンソル積の因子交換

## 概要
同じ基底の元を向きの生成元とする二つの prism の完備テンソル積を交換する。

## 方針
通常テンソル積の交換同型を二座標完備化に延長する。

## 規約
BS 著者版 Example 7.9 の包絡候補。生成元の一致を明示する。

## 使われ方
生成元剰余の計算で得た正則性を、包絡の普遍性で使う因子順へ移す。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.BhattScholze.Prismatic

open _root_.SerrePositivity.DerivedCompletion _root_.Algebra.TensorProduct

variable {p : ℕ} [Fact p.Prime] {U A E : Type u}
variable [CommRing U] [CommRing A] [CommRing E] [Algebra U A] [Algebra U E]
variable (P : OrientedPrism p A) (Q : OrientedPrism p E)
variable (a : U) (hP : algebraMap U A a = P.generator)
variable (hQ : algebraMap U E a = Q.generator)

/-- 概要：共通の生成元を持つ完備テンソル積の交換同型。
方針：通常の交換同型が二番目の完備化座標を保つことを確認する。
規約：BS 著者版 Example 7.9。二つの因子の有界性は不要。
使われ方：関係列への特殊化の計算と普遍性を接続する。 -/
@[expose] def _root_.SerrePositivity.BhattScholze.Semiperfectoid.lciEnvelopeTensorSwap :
    _root_.SerrePositivity.BhattScholze.PrismCompletedTensor (A := U) (C := E) P ≃+*
      _root_.SerrePositivity.BhattScholze.PrismCompletedTensor (A := U) (C := A) Q := by
  let e := (Algebra.TensorProduct.comm U A E).toRingEquiv
  have hd : e (includeLeftRingHom P.generator) = includeLeftRingHom Q.generator := by
    change (1 : E) ⊗ₜ[U] P.generator = Q.generator ⊗ₜ[U] (1 : A)
    rw [← hP, ← hQ]
    exact (tmul_one_eq_one_tmul a).symm
  exact pdCompletionRingEquiv e p _ _ hd

/-- 概要：因子交換は左の向きの生成元を右側の左生成元に送る。
方針：二座標完備化の単位公式とテンソル積の基底関係を用いる。
規約：BS 著者版 Example 7.9 の生成元を保つ同型。
使われ方：生成元の正則性と剰余の有界性の移送。 -/
theorem _root_.SerrePositivity.BhattScholze.Semiperfectoid.lciEnvelopeTensorSwap_generator :
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.lciEnvelopeTensorSwap P Q a hP hQ (_root_.SerrePositivity.BhattScholze.prismCompletedTensorLeft P P.generator) =
      _root_.SerrePositivity.BhattScholze.prismCompletedTensorLeft Q Q.generator := by
  unfold _root_.SerrePositivity.BhattScholze.Semiperfectoid.lciEnvelopeTensorSwap
  simp only [_root_.SerrePositivity.BhattScholze.prismCompletedTensorLeft, RingHom.comp_apply, pdCompletionRingEquiv_unit]
  congr 1
  change (1 : E) ⊗ₜ[U] P.generator = Q.generator ⊗ₜ[U] (1 : A)
  rw [← hP, ← hQ]
  exact (tmul_one_eq_one_tmul a).symm

end SerrePositivity.BhattScholze.Prismatic
