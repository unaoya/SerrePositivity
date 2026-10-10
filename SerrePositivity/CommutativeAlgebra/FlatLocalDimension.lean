module

public import SerrePositivity.CommutativeAlgebra.HilbertSamuel
public import SerrePositivity.CommutativeAlgebra.SupportDimension
public import Mathlib.RingTheory.LocalRing.Length
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-! # 極大イデアルを保つ平坦局所拡大

`m_A B = m_B` となる平坦局所拡大は長さ・環の次元・正則性を保つ。
長さは Mathlib の基底変更公式、次元は Samuel 関数の一致と既存の Hilbert–Samuel の
次元定理による。完備化と剰余体拡大に共通の保存則である。
-/

public section

universe u

namespace SerrePositivity

open IsLocalRing TensorProduct

set_option backward.isDefEq.respectTransparency false

section

variable (A B : Type u) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] [Module.Flat A B]
    (hm : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B)

include hm in
/-- 閉ファイバーが剰余体である平坦局所拡大は、任意の加群の長さを保つ。 -/
theorem length_baseChange_of_map_maximalIdeal
    (M : Type u) [AddCommGroup M] [Module A M] :
    Module.length B (B ⊗[A] M) = Module.length A M := by
  let : IsLocalHom (algebraMap A B) := ((local_hom_TFAE _).out 3 1).mp hm.le
  let : IsSimpleModule B (B ⧸ maximalIdeal B) :=
    isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp (maximalIdeal.isMaximal B))
  rw [IsLocalRing.length_baseChange A B M, hm,
    Module.length_eq_one B (B ⧸ maximalIdeal B), mul_one]

include hm in
/-- 極大イデアルを保つ平坦局所拡大では環自身の Samuel 関数が一致する。 -/
theorem samuelFunction_baseChange_of_map_maximalIdeal (n : ℕ) :
    HilbertSamuel.samuelFunction B (maximalIdeal B) B n =
      HilbertSamuel.samuelFunction A (maximalIdeal A) A n := by
  have hsA : ((maximalIdeal A) ^ n • ⊤ : Submodule A A) = (maximalIdeal A) ^ n := by
    exact (Ideal.smul_eq_mul _ _).trans (Ideal.mul_top _)
  have hsB : ((maximalIdeal B) ^ n • ⊤ : Submodule B B) = (maximalIdeal B) ^ n := by
    exact (Ideal.smul_eq_mul _ _).trans (Ideal.mul_top _)
  unfold HilbertSamuel.samuelFunction
  rw [hsA, hsB]
  rw [← hm, ← Ideal.map_pow,
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B
      ((maximalIdeal A) ^ n)).toLinearEquiv.length_eq]
  exact length_baseChange_of_map_maximalIdeal A B hm _

/-- 有限次元の環では自然数化した次元から元の Krull 次元が復元できる。 -/
theorem natCast_dimToNat_ringKrullDim (S : Type*) [CommRing S] [FiniteRingKrullDim S] :
    (dimToNat (ringKrullDim S) : WithBot ℕ∞) = ringKrullDim S := by
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp (ringKrullDim_ne_bot (R := S))
  have hdt : d ≠ ⊤ := by
    intro h
    apply ringKrullDim_ne_top (R := S)
    rw [← hd, h]
    rfl
  rw [← hd, dimToNat, WithBot.unbotD_coe, ← WithBot.coe_natCast, ENat.natCast_toNat hdt]

include hm in
/-- 極大イデアルを保つ Noether 平坦局所拡大は Krull 次元を保つ。
既存の Hilbert–Samuel 多項式の存在・次元定理を使う。 -/
theorem ringKrullDim_eq_of_flat_of_map_maximalIdeal [IsNoetherianRing A] [IsNoetherianRing B] :
    ringKrullDim B = ringKrullDim A := by
  obtain ⟨s, x, hx⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (maximalIdeal A).fg_of_isNoetherianRing
  obtain ⟨P, hP, _⟩ := HilbertSamuel.exists_isSamuelPoly A (maximalIdeal A)
    (maximalIdeal.isMaximal A).isPrime.radical x hx.symm A
  have hPB : HilbertSamuel.IsSamuelPoly B (maximalIdeal B) B P := by
    simpa only [HilbertSamuel.IsSamuelPoly,
      samuelFunction_baseChange_of_map_maximalIdeal A B hm] using hP
  have hdeg : dimToNat (ringKrullDim B) = dimToNat (ringKrullDim A) := by
    rw [← HilbertSamuel.natDegree_poly_eq_dim B (maximalIdeal B)
      (maximalIdeal.isMaximal B).isPrime.radical,
      ← HilbertSamuel.natDegree_poly_eq_dim A (maximalIdeal A)
        (maximalIdeal.isMaximal A).isPrime.radical,
      HilbertSamuel.poly_eq B hPB, HilbertSamuel.poly_eq A hP]
  rw [← natCast_dimToNat_ringKrullDim B, ← natCast_dimToNat_ringKrullDim A, hdeg]

include hm in
/-- 真のイデアルで商を取っても、極大イデアルを保つ平坦局所拡大の次元は一致する。 -/
theorem ringKrullDim_quotient_map_eq_of_flat_of_map_maximalIdeal
    [IsNoetherianRing A] [IsNoetherianRing B] (P : Ideal A) (hP : P ≠ ⊤) :
    ringKrullDim (B ⧸ P.map (algebraMap A B)) = ringKrullDim (A ⧸ P) := by
  let : Nontrivial (A ⧸ P) := Ideal.Quotient.nontrivial_iff.mpr hP
  let : IsLocalRing (A ⧸ P) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  have hPB : P.map (algebraMap A B) ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal B).ne_top
      ((Ideal.map_mono (le_maximalIdeal hP)).trans_eq hm)
  let : Nontrivial (B ⧸ P.map (algebraMap A B)) := Ideal.Quotient.nontrivial_iff.mpr hPB
  let : IsLocalRing (B ⧸ P.map (algebraMap A B)) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  let : IsNoetherianRing (A ⧸ P) :=
    isNoetherianRing_of_surjective A _ (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  let : IsNoetherianRing (B ⧸ P.map (algebraMap A B)) :=
    isNoetherianRing_of_surjective B _ (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  let : Module.Flat (A ⧸ P) (B ⧸ P.map (algebraMap A B)) :=
    Module.Flat.of_linearEquiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B P).toLinearEquiv
  have hmQ : (maximalIdeal (A ⧸ P)).map
      (algebraMap (A ⧸ P) (B ⧸ P.map (algebraMap A B))) =
      maximalIdeal (B ⧸ P.map (algebraMap A B)) := by
    rw [← map_maximalIdeal_of_surjective (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective,
      Ideal.map_map]
    change (maximalIdeal A).map
      ((Ideal.Quotient.mk (P.map (algebraMap A B))).comp (algebraMap A B)) = _
    rw [← Ideal.map_map, hm,
      map_maximalIdeal_of_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective]
  let : IsLocalHom (algebraMap (A ⧸ P) (B ⧸ P.map (algebraMap A B))) :=
    ((local_hom_TFAE _).out 3 1).mp hmQ.le
  exact ringKrullDim_eq_of_flat_of_map_maximalIdeal (A ⧸ P)
    (B ⧸ P.map (algebraMap A B)) hmQ

include hm in
/-- 有限生成加群の台の次元も、極大イデアルを保つ Noether 平坦局所拡大で保存される。
素イデアル商の次元比較から、短完全列と平坦性による帰納法で示す。 -/
theorem supportDim_baseChange_of_map_maximalIdeal [IsNoetherianRing A] [IsNoetherianRing B]
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    Module.supportDim B (B ⊗[A] M) = Module.supportDim A M := by
  have hM := (inferInstance : Module.Finite A M)
  induction hM using IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime A with
  | subsingleton M => simp [Module.supportDim_eq_bot_of_subsingleton]
  | quotient M P e =>
      rw [Module.supportDim_eq_of_equiv (LinearEquiv.baseChange A B _ _ e),
        Module.supportDim_eq_of_equiv e,
        ← Module.supportDim_eq_of_equiv
          (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B P.asIdeal).toLinearEquiv,
        Module.supportDim_quotient_eq_ringKrullDim, Module.supportDim_quotient_eq_ringKrullDim]
      exact ringKrullDim_quotient_map_eq_of_flat_of_map_maximalIdeal A B hm
        P.asIdeal P.isPrime.ne_top
  | exact M₁ M₂ M₃ f g hf hg he ih₁ ih₃ =>
      rw [supportDim_eq_max_of_exact (f.baseChange B) (g.baseChange B)
        (Module.Flat.lTensor_preserves_injective_linearMap (M := B) f hf)
        (g.baseChange_surjective B hg) (Module.Flat.lTensor_exact B he),
        supportDim_eq_max_of_exact f g hf hg he, ih₁, ih₃]

end

/-- 正則性は極大イデアルを保つ Noether 平坦局所拡大で保たれる。 -/
theorem isRegularLocalRing_of_flat_of_map_maximalIdeal
    (A B : Type u) [CommRing A] [CommRing B] [IsRegularLocalRing A]
    [IsLocalRing B] [IsNoetherianRing B] [Algebra A B] [Module.Flat A B]
    (hm : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) : IsRegularLocalRing B := by
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [ringKrullDim_eq_of_flat_of_map_maximalIdeal A B hm,
    ← (isRegularLocalRing_iff A).mp inferInstance]
  rw [← hm]
  exact_mod_cast Ideal.spanFinrank_map_le_of_fg (algebraMap A B)
    (maximalIdeal A).fg_of_isNoetherianRing

end SerrePositivity
