module
public meta import SerrePositivity.Util.Citation

public import SerrePositivity.BhattScholze.Semiperfectoid.Lci.LciEnvelopeExistence
public import SerrePositivity.BhattScholze.Semiperfectoid.Lci.LciEnvelopeDiscrete
public import SerrePositivity.BhattScholze.Semiperfectoid.Lci.LciEnvelopeTensorSwap
public import SerrePositivity.BhattScholze.Prism.Basic.UniversalOriented
public import SerrePositivity.BhattScholze.Semiperfectoid.Lci.RawVariableEnvelopeFaithful
public import SerrePositivity.BhattScholze.Semiperfectoid.Lci.PerfectEnvelopeInitial
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.OfFaithfullyFlat
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# 正則列の有界な包絡の完全忠実平坦な剰余単位

## 概要
既存の有界な正則列包絡に、指定した関係商上の完全忠実平坦な剰余単位を加える。

## 方針
普遍向き付き prism 上の自由変数包絡を分類射で特殊化し、完備テンソル積の剰余で有界性を確認する。

## 規約
BS 著者版 Example 7.9 。関係商 R の p 冪ねじれを有界とする。

## 使われ方
lci 商の site の始対象の構成。任意の有界 prism 上の対象への普遍性に追加条件は課さない。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

universe u

namespace SerrePositivity.BhattScholze.Prismatic

open _root_.CategoryTheory _root_.SerrePositivity.DerivedCompletion
open scoped _root_.TensorProduct

variable {p : ℕ} [Fact p.Prime] {A₀ A S : Type u} [CommRing A₀] [CommRing A]
variable (P₀ : OrientedPrism p A₀) (P : OrientedPrism p A) {r : ℕ} (f : Fin r → A)
variable (index : Fin r ≃ S) (g : OrientedPrism.Hom P₀ P)

local notation "U" => RelativeFreeDeltaRing (R := A₀) S
local notation "C" => (MvPolynomial.C : A₀ →+* U)
local notation "a" => C P₀.generator
local notation "D" => relativeFreeDeltaStructure S P₀.deltaStructure
local notation "c" => relativeFreeDeltaEval P.deltaStructure g.toRingHom (fun s : S => f (index.symm s))
local notation "E" => completedFreeDelta P₀ S
local notation "α" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.rawVariableEnvelopeMap P₀ S
local notation "K" => (Ideal.span {a} : Ideal U) ⊔
  Ideal.span (Set.range fun s : S => MvPolynomial.X (s, 0))

include index in
/-- 概要：p 正則な普遍分類基底から、正則列の有界な包絡を作れる。
方針：剰余で得た正則性を因子交換で移し、既存の包絡の完備底変換を適用する。
規約：BS 著者版 Example 7.9。R の有界性だけを標的商に仮定する。
使われ方：普遍向き付き prism による一般の存在定理。 -/
theorem _root_.SerrePositivity.BhattScholze.Semiperfectoid.exists_bounded_lciRelationEnvelope_faithful_of_classifier
    (hP₀ : _root_.SerrePositivity.BhattScholze.Prismatic.IsBoundedPrism P₀) (hd : g.toRingHom P₀.generator = P.generator)
    (hp₀ : Function.Injective (fun x : A₀ => (p : A₀) * x))
    (hpd₀ : Function.Injective (fun x : A₀ ⧸ P₀.ideal => (p : A₀ ⧸ P₀.ideal) * x))
    (hf : _root_.SerrePositivity.IsKoszulResolution (fun i => Ideal.Quotient.mk P.ideal (f i)))
    (hR : ∃ N : ℕ, ∀ (n : ℕ) (x : A ⧸ (P.ideal ⊔ Ideal.span (Set.range f))),
      (p : A ⧸ (P.ideal ⊔ Ideal.span (Set.range f))) ^ n * x = 0 →
        (p : A ⧸ (P.ideal ⊔ Ideal.span (Set.range f))) ^ N * x = 0) :
    ∃ (B : CommRingCat.{u}) (Q : _root_.SerrePositivity.BhattScholze.OrientedPrism p B) (η : A →+* B),
      ∃ hE : _root_.SerrePositivity.BhattScholze.Semiperfectoid.IsFiniteLciRelationEnvelope P f Q η, _root_.SerrePositivity.BhattScholze.Prismatic.IsBoundedPrism Q ∧
        letI := (_root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectEnvelopeResidueUnit
          (show P.ideal ≤ P.ideal ⊔ Ideal.span (Set.range f) from le_sup_left) hE).toAlgebra
        _root_.SerrePositivity.IsCompletelyFaithfullyFlat (Ideal.span {(p : A ⧸ (P.ideal ⊔ Ideal.span (Set.range f)))})
          (B ⧸ Q.ideal) := by
  let := pdCompletionCommRing U p a
  obtain ⟨Q, hgen, hEnv, hregular, hbound⟩ :=
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.exists_lciRelation_regular_completedTensor P₀ P f index g hP₀ hd hp₀ hpd₀ hf hR
  let := (c).toAlgebra
  let := (α).toAlgebra
  have hca : c a = P.generator := by rw [_root_.SerrePositivity.BhattScholze.relativeFreeDeltaEval_C, hd]
  have hαa : α a = Q.generator := by
    rw [_root_.SerrePositivity.BhattScholze.Semiperfectoid.rawVariableEnvelopeMap_C]
    exact hgen.symm
  let H := _root_.SerrePositivity.BhattScholze.PrismCompletedTensor (A := U) («C» := E) P
  let H' := _root_.SerrePositivity.BhattScholze.PrismCompletedTensor (A := U) («C» := A) Q
  let l : A →+* H := _root_.SerrePositivity.BhattScholze.prismCompletedTensorLeft P
  let l' : E →+* H' := _root_.SerrePositivity.BhattScholze.prismCompletedTensorLeft Q
  let e : H ≃+* H' := _root_.SerrePositivity.BhattScholze.Semiperfectoid.lciEnvelopeTensorSwap P Q a hca hαa
  have hed : e (l P.generator) = l' Q.generator :=
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.lciEnvelopeTensorSwap_generator P Q a hca hαa
  have hreg : IsRegular (l P.generator) := by
    have hi : Function.Injective (fun x : H => l P.generator * x) := by
      intro x y hxy
      apply e.injective
      apply hregular.1
      simpa only [map_mul, hed] using congrArg e hxy
    exact ⟨hi, fun x y h => hi (by simpa only [mul_comm] using h)⟩
  have hc : (D).IsDeltaHom P.deltaStructure c :=
    _root_.SerrePositivity.BhattScholze.relativeFreeDeltaEval_isDeltaHom P₀.deltaStructure P.deltaStructure g.toRingHom g.map_delta _
  have hg : (c).comp C = g.toRingHom := by
    apply RingHom.ext
    intro x
    change c (C x) = g.toRingHom x
    exact _root_.SerrePositivity.BhattScholze.relativeFreeDeltaEval_C P.deltaStructure g.toRingHom _ x
  obtain ⟨Q', hgen', hEnv'⟩ := _root_.SerrePositivity.BhattScholze.Semiperfectoid.exists_envelope_of_classified_ideal_of_regular P₀ P D C
    (_root_.SerrePositivity.BhattScholze.relativeFreeDeltaStructure_C_isDeltaHom S P₀.deltaStructure) K
    ((show Ideal.span {a} ≤ K from le_sup_left) (Ideal.subset_span (Set.mem_singleton _)))
    Q α hEnv c hc g hg hd hreg
  have hK : (K).map c = (P.ideal ⊔ Ideal.span (Set.range f)) := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, hca, Ideal.map_span]
    change Ideal.span {P.generator} ⊔ Ideal.span _ =
      Ideal.span {P.generator} ⊔ Ideal.span (Set.range f)
    congr 2
    ext x
    constructor
    · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
      refine ⟨index.symm s, ?_⟩
      rw [_root_.SerrePositivity.BhattScholze.relativeFreeDeltaEval_X, Function.iterate_zero_apply]
    · rintro ⟨i, rfl⟩
      refine ⟨MvPolynomial.X (index i, 0), ⟨index i, rfl⟩, ?_⟩
      rw [_root_.SerrePositivity.BhattScholze.relativeFreeDeltaEval_X, Function.iterate_zero_apply, index.symm_apply_apply]
  have hI : Q'.ideal = Ideal.span {l P.generator} := by
    change Ideal.span {Q'.generator} = _
    rw [hgen']
  have hmap : Q'.ideal.map e.toRingHom = Ideal.span {l' Q.generator} := by
    rw [hI, Ideal.map_span, Set.image_singleton]
    change Ideal.span {e (l P.generator)} = Ideal.span {l' Q.generator}
    rw [hed]
  let eq : H ⧸ Q'.ideal ≃+* H' ⧸ Ideal.span {l' Q.generator} :=
    Ideal.quotientEquiv _ _ e hmap.symm
  have hb : _root_.SerrePositivity.BhattScholze.Prismatic.IsBoundedPrism Q' := by
    obtain ⟨N, hN⟩ := hbound
    refine ⟨N, fun n x hx => ?_⟩
    apply eq.injective
    have hx' : (p : H' ⧸ Ideal.span {l' Q.generator}) ^ n * eq x = 0 := by
      simpa only [map_mul, map_pow, map_natCast, map_zero] using congrArg eq hx
    simpa only [map_mul, map_pow, map_natCast, map_zero] using hN n (eq x) hx'
  have hE : _root_.SerrePositivity.BhattScholze.Semiperfectoid.IsFiniteLciRelationEnvelope P f Q' l := by
    simpa only [_root_.SerrePositivity.BhattScholze.Semiperfectoid.IsFiniteLciRelationEnvelope, hK] using hEnv'
  refine ⟨CommRingCat.of H, Q', l, hE, hb, ?_⟩
  have hF := _root_.SerrePositivity.BhattScholze.Semiperfectoid.rawVariableEnvelope_residue_completelyFaithfullyFlat
    (S := S) P₀ hp₀ hpd₀ Q hgen hEnv.map_le
  have hRA : ∃ N : ℕ, ∀ (n : ℕ) (x : A ⧸ (K).map c),
      (p : A ⧸ (K).map c)^n * x = 0 → (p : A ⧸ (K).map c)^N * x = 0 := by
    let Bound (J : Ideal A) : Prop := ∃ N : ℕ, ∀ (n : ℕ) (x : A ⧸ J),
      (p : A ⧸ J)^n * x = 0 → (p : A ⧸ J)^N * x = 0
    exact Eq.mp (congrArg Bound hK.symm) hR
  obtain ⟨v', hv', hfv'⟩ := _root_.SerrePositivity.BhattScholze.Semiperfectoid.exists_prismCompletedTensor_relationResidue_faithful
    (A := A) Q K hEnv.map_le hF hRA
  let R₁ := A ⧸ (P.ideal ⊔ Ideal.span (Set.range f))
  let R₂ := A ⧸ (K).map c
  let eR : R₁ ≃+* R₂ := Ideal.quotEquivOfEq hK.symm
  let v0 : R₂ →+* H' ⧸ Ideal.span {l' Q.generator} := v'
  have hfv0 : letI := v0.toAlgebra
      _root_.SerrePositivity.IsCompletelyFaithfullyFlat (Ideal.span {(p : R₂)}) (H' ⧸ Ideal.span {l' Q.generator}) := hfv'
  have hv0 (x : A) : v0 (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (_root_.SerrePositivity.BhattScholze.prismCompletedTensorRight Q x) := hv' x
  let ψ := v0.comp eR.toRingHom
  let v := eq.symm.toRingHom.comp ψ
  have heR : letI := eR.toRingHom.toAlgebra
      _root_.SerrePositivity.IsCompletelyFaithfullyFlat (Ideal.span {(p : R₁)}) R₂ := by
    letI := eR.toRingHom.toAlgebra
    letI : Module.FaithfullyFlat R₁ R₂ := by
      apply RingHom.faithfullyFlat_algebraMap_iff.mp
      exact RingHom.FaithfullyFlat.of_bijective eR.bijective
    exact _root_.SerrePositivity.isCompletelyFaithfullyFlat_of_faithfullyFlat _
  have hψ : letI := ψ.toAlgebra
      _root_.SerrePositivity.IsCompletelyFaithfullyFlat (Ideal.span {(p : R₁)}) (H' ⧸ Ideal.span {l' Q.generator}) := by
    exact _root_.SerrePositivity.BhattScholze.Andre.Transfinite.isCompletelyFaithfullyFlat_comp eR.toRingHom v0
      (Ideal.span {(p : R₁)}) heR (by
        simpa only [Ideal.map_span, Set.image_singleton, map_natCast] using hfv0)
  have hv : letI := v.toAlgebra
      _root_.SerrePositivity.IsCompletelyFaithfullyFlat (Ideal.span {(p : R₁)}) (H ⧸ Q'.ideal) := by
    apply _root_.SerrePositivity.BhattScholze.Andre.Transfinite.isCompletelyFaithfullyFlat_comp ψ eq.symm.toRingHom _ hψ
    letI := eq.symm.toRingHom.toAlgebra
    letI : Module.FaithfullyFlat (H' ⧸ Ideal.span {l' Q.generator}) (H ⧸ Q'.ideal) := by
      apply RingHom.faithfullyFlat_algebraMap_iff.mp
      exact RingHom.FaithfullyFlat.of_bijective eq.symm.bijective
    exact _root_.SerrePositivity.isCompletelyFaithfullyFlat_of_faithfullyFlat _
  have hswap (x : A) : e (l x) = _root_.SerrePositivity.BhattScholze.prismCompletedTensorRight Q x := by
    letI : Algebra U A := (c).toAlgebra
    letI : Algebra U E := (α).toAlgebra
    letI : Module U A := Algebra.toModule
    letI : Module U E := Algebra.toModule
    unfold e l _root_.SerrePositivity.BhattScholze.Semiperfectoid.lciEnvelopeTensorSwap
    change pdCompletionRingEquiv (Algebra.TensorProduct.comm U A E).toRingEquiv p
      (Algebra.TensorProduct.includeLeftRingHom P.generator)
      (Algebra.TensorProduct.includeLeftRingHom Q.generator) _
      (pdCompletionUnit (A ⊗[U] E) p _ (x ⊗ₜ[U] (1 : E))) =
      pdCompletionUnit (E ⊗[U] A) p _ ((1 : E) ⊗ₜ[U] x)
    rw [pdCompletionRingEquiv_unit]
    rfl
  have hveq : v = _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectEnvelopeResidueUnit
      (show P.ideal ≤ P.ideal ⊔ Ideal.span (Set.range f) from le_sup_left) hE := by
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro x
    apply eq.injective
    change eq (eq.symm (v0 (eR (Ideal.Quotient.mk _ x)))) = eq (Ideal.Quotient.mk _ (l x))
    rw [eq.apply_symm_apply, Ideal.quotEquivOfEq_mk, hv0]
    change Ideal.Quotient.mk _ (_root_.SerrePositivity.BhattScholze.prismCompletedTensorRight Q x) = Ideal.Quotient.mk _ (e (l x))
    rw [hswap]
  rw [← hveq]
  exact hv

/-- 概要：生成元剰余で Koszul 正則な有限列は、その商が有界なら有界な包絡を持つ。
方針：普遍向き付き prism と有限添字の宇宙持ち上げに前の構成を適用する。
規約：BS 著者版 Example 7.9 。R は有界、任意の有界 prism 上の対象には追加条件なし。
使われ方：lci 商の包絡と site の始対象。 -/
theorem _root_.SerrePositivity.BhattScholze.Semiperfectoid.exists_bounded_lciRelationEnvelope_faithful
    (hf : ∀ n : ℕ, Limits.IsZero
      ((_root_.SerrePositivity.koszulComplex (fun i => Ideal.Quotient.mk P.ideal (f i))).homology (-(n + 1 : ℤ))))
    (hR : ∃ N : ℕ, ∀ (n : ℕ) (x : A ⧸ (P.ideal ⊔ Ideal.span (Set.range f))),
      (p : A ⧸ (P.ideal ⊔ Ideal.span (Set.range f))) ^ n * x = 0 →
        (p : A ⧸ (P.ideal ⊔ Ideal.span (Set.range f))) ^ N * x = 0) :
    ∃ (B : CommRingCat.{u}) (Q : _root_.SerrePositivity.BhattScholze.OrientedPrism p B) (η : A →+* B),
      ∃ hE : _root_.SerrePositivity.BhattScholze.Semiperfectoid.IsFiniteLciRelationEnvelope P f Q η, _root_.SerrePositivity.BhattScholze.Prismatic.IsBoundedPrism Q ∧
        letI := (_root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectEnvelopeResidueUnit
          (show P.ideal ≤ P.ideal ⊔ Ideal.span (Set.range f) from le_sup_left) hE).toAlgebra
        _root_.SerrePositivity.IsCompletelyFaithfullyFlat (Ideal.span {(p : A ⧸ (P.ideal ⊔ Ideal.span (Set.range f)))})
          (B ⧸ Q.ideal) := by
  obtain ⟨g, hd, _⟩ := _root_.SerrePositivity.BhattScholze.existsUnique_universalOrientedPrismHom p P
  exact _root_.SerrePositivity.BhattScholze.Semiperfectoid.exists_bounded_lciRelationEnvelope_faithful_of_classifier (_root_.SerrePositivity.BhattScholze.universalOrientedPrism.{u} p) P f
    (Equiv.ulift.symm : Fin r ≃ ULift.{u} (Fin r)) g (_root_.SerrePositivity.BhattScholze.universalOrientedPrism_bounded p) hd
    (_root_.SerrePositivity.BhattScholze.universalOrientedPrism_regular p).1 (_root_.SerrePositivity.BhattScholze.universalOrientedPrism_mod_generator_p_regular p)
    (_root_.SerrePositivity.isKoszulResolution_of_negative_homology _ hf) hR

end SerrePositivity.BhattScholze.Prismatic

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Ex 7.9" (partial := component) "BS-W15 K5（11-11）：envelope の側は本体（R の有界性を仮定する原典の形、D76。結論は有界な prism）。p 反転の議論 G-A3-7 の古典的な入力（余法加群、分冪の像の稠密性）も本体。Δ_R/A との同一視と HT 比較の適用は drafts の A3/LciAndQuasiregular"] _root_.SerrePositivity.BhattScholze.Semiperfectoid.exists_bounded_lciRelationEnvelope_faithful
