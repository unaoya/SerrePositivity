module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.CommutativeAlgebra.DividedPowers.FreeDPBasis
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false

/-!
# 元の族に沿う分冪表示

## 概要
自由分冪代数で各一次分冪を指定した元に等しくする（BS 著者版 Lemma 2.38 の表示）。

## 方針
分冪単項式の基底で射の一意性を示す。評価射には自由分冪代数の普遍性を使う。

## 規約
表示は任意の係数環と任意の添字集合に対して定義する。

## 使われ方
有限 Koszul 正則列に沿う分冪包。
-/

public noncomputable section

universe u v w

namespace SerrePositivity.BhattScholze

variable {A : Type u} [CommRing A] {σ : Type v} (a : σ → A)

local notation "G" => DividedPowerAlgebra A (σ →₀ A)
local notation "γ[" s "," n "]" => DividedPowerAlgebra.dp A n (Finsupp.single s 1 : σ →₀ A)

/-- 概要：各一次分冪を与えられた元に等しくする関係イデアル。
方針：自由分冪代数で γ₁(e_s) − a_s の生成するイデアルを取る。
規約：BS 著者版 Lemma 2.38 の通常の押し出し表示。
使われ方：族に沿う分冪表示環。 -/
@[expose] def dpFamilyRelationIdeal : Ideal G :=
  Ideal.span (Set.range fun s => γ[s, 1] - algebraMap A G (a s))

/-- 概要：元の族に沿う分冪表示環。
方針：自由分冪代数に各一次分冪の関係式を課す。
規約：BS 著者版 Lemma 2.38 の環の表示。正則性は定理で使う。
使われ方：分冪包、係数拡大、Frobenius 除算の比較。 -/
abbrev DPFamilyPresentation := G ⧸ dpFamilyRelationIdeal a

/-- 概要：表示環内の各座標の分冪の像。
方針：自由分冪代数の標準分冪を商に写す。
規約：BS 著者版 Lemma 2.38 の標準生成元。
使われ方：標的への写像の指定。 -/
def dpFamilyGenerator (s : σ) (n : ℕ) : DPFamilyPresentation a :=
  Ideal.Quotient.mk (dpFamilyRelationIdeal a) (γ[s, n])

/-- 概要：表示環の一次分冪は指定した係数に等しい。
方針：定義関係を商で零にする。
規約：BS 著者版 Lemma 2.38 の表示。
使われ方：高次分冪の階乗関係。 -/
theorem dpFamilyGenerator_one (s : σ) :
    dpFamilyGenerator a s 1 = Ideal.Quotient.mk (dpFamilyRelationIdeal a) (algebraMap A G (a s)) := by
  apply sub_eq_zero.mp
  change Ideal.Quotient.mk (dpFamilyRelationIdeal a) (γ[s, 1]) -
    Ideal.Quotient.mk (dpFamilyRelationIdeal a) (algebraMap A G (a s)) = 0
  rw [← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self s))

/-- 概要：表示環内の階乗を払うと通常の冪になる。
方針：自由分冪代数での階乗恒等式を商に移す。
規約：BS 著者版 Lemma 2.38 の表示。
使われ方：p 反転後の係数環との比較。 -/
theorem dpFamilyGenerator_factorial_mul (s : σ) (n : ℕ) :
    (n.factorial : DPFamilyPresentation a) * dpFamilyGenerator a s n =
      (Ideal.Quotient.mk (dpFamilyRelationIdeal a) (algebraMap A G (a s))) ^ n := by
  have h := congrArg (Ideal.Quotient.mk (dpFamilyRelationIdeal a))
    (DividedPowerAlgebra.natFactorial_mul_dp_eq (R := A) n (Finsupp.single s 1 : σ →₀ A))
  simp only [map_mul, map_natCast, map_pow] at h
  change (n.factorial : DPFamilyPresentation a) * dpFamilyGenerator a s n =
    dpFamilyGenerator a s 1 ^ n at h
  rwa [dpFamilyGenerator_one] at h

variable {B : Type w} [CommRing B] [Algebra A B] {I : Ideal B}

/-- 概要：表示環からの A 代数射は各座標の分冪で決まる。
方針：自由分冪代数に引き戻し、分冪単項式の基底上で一致させる。
規約：BS 著者版 Lemma 2.38 の生成元。
使われ方：任意の分冪標的への普遍射の一意性。 -/
theorem dpFamilyHom_ext (F H : DPFamilyPresentation a →ₐ[A] B)
    (h : ∀ s n, F (dpFamilyGenerator a s n) = H (dpFamilyGenerator a s n)) : F = H := by
  apply Ideal.Quotient.algHom_ext A
  apply AlgHom.toLinearMap_injective
  apply (freeDPBasis σ A).ext
  intro m
  simp only [AlgHom.toLinearMap_apply, freeDPBasis_apply, AlgHom.comp_apply,
    freeDPMonomial, Finsupp.prod, map_prod]
  apply Finset.prod_congr rfl
  intro s _
  exact h s (m s)

/-- 概要：各 a_s が分冪イデアルに写る標的への実評価射。
方針：自由分冪代数の普遍射で一次分冪の関係を零にする。
規約：標的の p ねじれを許す（BS 著者版 Lemma 2.38 の分冪普遍性）。
使われ方：正則列の分冪包の普遍性。 -/
def dpFamilyEval (H : DividedPowers I) (ha : ∀ s, algebraMap A B (a s) ∈ I) :
    DPFamilyPresentation a →ₐ[A] B := by
  let g : (σ →₀ A) →ₗ[A] B := Finsupp.linearCombination A (algebraMap A B ∘ a)
  have hg (s : σ) : g (Finsupp.single s 1) = algebraMap A B (a s) := by
    simp [g]
  have hgI (m : σ →₀ A) : g m ∈ I := by
    classical
    rw [show g m = m.sum (fun s b => b • algebraMap A B (a s)) from
      Finsupp.linearCombination_apply _ _]
    exact I.sum_mem fun s _ => by
      change m s • algebraMap A B (a s) ∈ I
      rw [Algebra.smul_def]
      exact I.mul_mem_left _ (ha s)
  let F := DividedPowerAlgebra.lift H g hgI
  refine Ideal.Quotient.liftₐ (dpFamilyRelationIdeal a) F ?_
  have hker : dpFamilyRelationIdeal a ≤ RingHom.ker F.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨s, rfl⟩
    change F (γ[s, 1] - algebraMap A G (a s)) = 0
    rw [map_sub, DividedPowerAlgebra.lift_apply_dp, hg, H.dpow_one (ha s),
      AlgHom.commutes, sub_self]
  exact fun _ hx => hker hx

/-- 概要：分冪標的への評価は標準生成元を対応する分冪に送る。
方針：自由分冪代数の普遍射の式を適用する。
規約：BS 著者版 Lemma 2.38 の分冪普遍性。
使われ方：表示環の分冪包との同定。 -/
theorem dpFamilyEval_generator (H : DividedPowers I)
    (ha : ∀ s, algebraMap A B (a s) ∈ I) (s : σ) (n : ℕ) :
    dpFamilyEval a H ha (dpFamilyGenerator a s n) = H.dpow n (algebraMap A B (a s)) := by
  simp [dpFamilyEval, dpFamilyGenerator, Ideal.Quotient.liftₐ_apply,
    DividedPowerAlgebra.lift_apply_dp]

/-- 概要：標準分冪の値を指定すると、分冪標的への A 代数射は一意。
方針：評価射の公式と分冪単項式での外延性を合わせる。
規約：BS 著者版 Lemma 2.38 の表示の普遍性。
使われ方：分冪包としての一意性。 -/
theorem existsUnique_dpFamilyEval (H : DividedPowers I)
    (ha : ∀ s, algebraMap A B (a s) ∈ I) :
    ∃! F : DPFamilyPresentation a →ₐ[A] B,
      ∀ s n, F (dpFamilyGenerator a s n) = H.dpow n (algebraMap A B (a s)) := by
  refine ⟨dpFamilyEval a H ha, dpFamilyEval_generator a H ha, ?_⟩
  intro F hF
  exact dpFamilyHom_ext a _ _ fun s n => (hF s n).trans (dpFamilyEval_generator a H ha s n).symm

end SerrePositivity.BhattScholze

open scoped TensorProduct

namespace SerrePositivity.BhattScholze

variable {A : Type u} {B : Type w} [CommRing A] [CommRing B] [Algebra A B]
  {σ : Type v} (a : σ → A)

local notation "G" => DividedPowerAlgebra A (σ →₀ A)
local notation "G'" => DividedPowerAlgebra B (σ →₀ B)
local notation "e" => freeDPBaseChangeEquiv σ A B
local notation "j" => ((Algebra.TensorProduct.includeRight (R := A) (A := B) (B := G)).toRingHom)
local notation "a'" => (algebraMap A B ∘ a)

local instance : CommRing G :=
  RingCon.instCommRingQuotient (DividedPowerAlgebra.ringCon A (σ →₀ A))

local instance : CommRing G' :=
  RingCon.instCommRingQuotient (DividedPowerAlgebra.ringCon B (σ →₀ B))

/-- 概要：自由分冪の標準生成元は係数拡大で対応する生成元に写る。
方針：一座標だけの分冪単項式に直して既存の係数拡大公式を適用する。
規約：BS 著者版 Lemma 2.38 の標準生成元。
使われ方：分冪表示の底変換と剰余での関係式。 -/
theorem freeDPBaseChangeEquiv_dp (s : σ) (n : ℕ) :
    e (1 ⊗ₜ[A] DividedPowerAlgebra.dp A n (Finsupp.single s 1)) =
      DividedPowerAlgebra.dp B n (Finsupp.single s 1) := by
  have hA : freeDPMonomial σ A (Finsupp.single s n) =
      DividedPowerAlgebra.dp A n (Finsupp.single s 1) :=
    Finsupp.prod_single_index DividedPowerAlgebra.dp_zero
  have hB : freeDPMonomial σ B (Finsupp.single s n) =
      DividedPowerAlgebra.dp B n (Finsupp.single s 1) :=
    Finsupp.prod_single_index DividedPowerAlgebra.dp_zero
  rw [← hA, ← hB, freeDPBaseChangeEquiv_apply, freeDPBaseChangeMap_monomial]

private theorem dpFamilyBaseChange_relation (s : σ) :
    e (j (DividedPowerAlgebra.dp A 1 (Finsupp.single s 1) - algebraMap A G (a s))) =
      DividedPowerAlgebra.dp B 1 (Finsupp.single s 1) - algebraMap B G' (a' s) := by
  rw [map_sub, map_sub]
  congr 1
  · exact freeDPBaseChangeEquiv_dp (A := A) (B := B) s 1
  · rw [freeDPBaseChangeEquiv_apply]
    change freeDPBaseChangeMap σ A B (1 ⊗ₜ[A] algebraMap A G (a s)) =
        algebraMap B G' (a' s)
    change (1 : G') * DividedPowerAlgebra.map B (freeDPCoefficientMap σ A B)
      (algebraMap A G (a s)) = _
    rw [one_mul]
    exact (DividedPowerAlgebra.map B (freeDPCoefficientMap σ A B)).commutes (a s)

private theorem dpFamilyBaseChange_ideal :
    dpFamilyRelationIdeal a' = ((dpFamilyRelationIdeal a).map j).map (e).toRingHom := by
  simp only [dpFamilyRelationIdeal, Ideal.map_span, ← Set.range_comp', Function.comp_def]
  exact congrArg (fun F : σ → G' => Ideal.span (Set.range F))
    (funext fun s => (dpFamilyBaseChange_relation a s).symm)

/-- 概要：族に沿う分冪表示は任意の係数拡大と可換。
方針：自由分冪代数の底変換と一次関係の計算を商テンソルの同型でつなぐ。
規約：正則性は表示環が分冪包になるために使う（BS 著者版 Lemma 2.38）。
使われ方：正則列の分冪包の底変換。 -/
def dpFamilyBaseChangeEquiv :
    (B ⊗[A] (G ⧸ dpFamilyRelationIdeal a)) ≃ₐ[B] (G' ⧸ dpFamilyRelationIdeal a') :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := A) B G B
    (dpFamilyRelationIdeal a)).trans
    (Ideal.quotientEquivAlg _ _ e (dpFamilyBaseChange_ideal a))

/-- 概要：分冪表示の底変換は各座標の標準分冪を保つ。
方針：商テンソル同型を代表元で計算して、自由分冪の底変換公式を使う。
規約：BS 著者版 Lemma 2.38 の底変換。
使われ方：異なる係数環の分冪包を結晶サイトの標準脚に沿って比べる。 -/
theorem dpFamilyBaseChangeEquiv_generator (s : σ) (n : ℕ) :
    dpFamilyBaseChangeEquiv (B := B) a (1 ⊗ₜ[A] dpFamilyGenerator a s n) =
      dpFamilyGenerator a' s n := by
  dsimp only [dpFamilyBaseChangeEquiv, dpFamilyGenerator]
  rw [AlgEquiv.trans_apply, Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul]
  change Ideal.Quotient.mk (dpFamilyRelationIdeal a')
    (e (1 ⊗ₜ[A] DividedPowerAlgebra.dp A n (Finsupp.single s 1))) = _
  rw [freeDPBaseChangeEquiv_dp]

end SerrePositivity.BhattScholze

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Lemma 2.38"] _root_.SerrePositivity.BhattScholze.dpFamilyBaseChangeEquiv
