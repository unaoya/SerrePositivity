module

public import SerrePositivity.BhattScholze.FreeDeltaFrobeniusModPFlat
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-! # 自由δ環Frobeniusの指定変数による実剰余射の忠実平坦性

対象はL/(p,z)→L/(p,φ(z))の通常射。完備化後の完全忠実平坦性は別工程。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (σ : Type u)
attribute [local instance] freeDeltaModPFrobeniusAlgebra
local notation "L₀" => FreeDeltaRing σ
local notation "R₀" => ModP L₀ p
local notation "B₀" => FreeDeltaModPFrobeniusTarget p σ

/-- 自由δ環の(p,x)商を、mod p環のx像の商に移す既存二重商同型。 -/
def freeDeltaPairModPEquiv (x : L₀) :
    (L₀ ⧸ Ideal.span {(p : L₀), x}) ≃+*
      (R₀ ⧸ Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : L₀)}) x}) :=
  (Ideal.quotEquivOfEq (Ideal.span_insert (p : L₀) {x})).trans
    ((DoubleQuot.quotQuotEquivQuotSup (Ideal.span {(p : L₀)}) (Ideal.span {x})).symm.trans
      (Ideal.quotEquivOfEq (by rw [Ideal.map_span, Set.image_singleton])))

omit [Fact p.Prime] in
/-- 二重商比較は元の自由環の標準像と両立する。 -/
theorem freeDeltaPairModPEquiv_mk (x y : L₀) :
    freeDeltaPairModPEquiv p σ x (Ideal.Quotient.mk _ y) =
      Ideal.Quotient.mk _ (Ideal.Quotient.mk _ y) := by
  rw [freeDeltaPairModPEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingEquiv.trans_apply, DoubleQuot.quotQuotEquivQuotSup_symm_quotQuotMk]
  rfl

/-- 指定変数のmod p像の主イデアル。 -/
abbrev freeDeltaFrobeniusCoordinateIdeal (s : σ) : Ideal R₀ :=
  Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : L₀)}) (MvPolynomial.X (s, 0))}

/-- 実mod p Frobenius作用による指定変数イデアルの拡大。 -/
abbrev freeDeltaFrobeniusCoordinateTargetIdeal (s : σ) : Ideal B₀ :=
  (freeDeltaFrobeniusCoordinateIdeal p σ s).map (algebraMap R₀ B₀)

omit [Fact p.Prime] in
/-- 拡大イデアルはφ(z)の実mod p像で生成される。 -/
theorem freeDeltaFrobeniusCoordinateTargetIdeal_eq (s : σ) :
    freeDeltaFrobeniusCoordinateTargetIdeal p σ s =
      (Ideal.span {(Ideal.Quotient.mk (Ideal.span {(p : L₀)})
        (freeDeltaFrobenius p σ (MvPolynomial.X (s, 0))))}).map
        (ULift.ringEquiv : B₀ ≃+* R₀).symm.toRingHom := by
  rw [freeDeltaFrobeniusCoordinateTargetIdeal, freeDeltaFrobeniusCoordinateIdeal,
    Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton]
  rfl

/-- 実通常商L/(p,φ(z))を忠実平坦基底変更の対象商へ移す同型。 -/
def freeDeltaFrobeniusCoordinateTargetEquiv (s : σ) :
    (L₀ ⧸ Ideal.span {(p : L₀), freeDeltaFrobenius p σ (MvPolynomial.X (s, 0))}) ≃+*
      (B₀ ⧸ freeDeltaFrobeniusCoordinateTargetIdeal p σ s) :=
  (freeDeltaPairModPEquiv p σ (freeDeltaFrobenius p σ (MvPolynomial.X (s, 0)))).trans
    (Ideal.quotientEquiv _ _ (ULift.ringEquiv : B₀ ≃+* R₀).symm
      (freeDeltaFrobeniusCoordinateTargetIdeal_eq p σ s))

omit [Fact p.Prime] in
/-- 対象商の比較は元の自由環の標準像を実剰余像へ送る。 -/
theorem freeDeltaFrobeniusCoordinateTargetEquiv_mk (s : σ) (y : L₀) :
    freeDeltaFrobeniusCoordinateTargetEquiv p σ s (Ideal.Quotient.mk _ y) =
      Ideal.Quotient.mk _ (ULift.up (Ideal.Quotient.mk (Ideal.span {(p : L₀)}) y)) := by
  rw [freeDeltaFrobeniusCoordinateTargetEquiv, RingEquiv.trans_apply,
    freeDeltaPairModPEquiv_mk, Ideal.quotientEquiv_mk]
  rfl

/-- 指定変数の商で基底変更した実mod p Frobenius作用の商環は忠実平坦。 -/
theorem freeDeltaFrobeniusCoordinateQuotient_moduleFaithfullyFlat (s : σ) :
    Module.FaithfullyFlat (R₀ ⧸ freeDeltaFrobeniusCoordinateIdeal p σ s)
      (B₀ ⧸ freeDeltaFrobeniusCoordinateTargetIdeal p σ s) := by
  let := freeDeltaModPFrobenius_moduleFaithfullyFlat p σ
  exact Module.FaithfullyFlat.of_linearEquiv _ _
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B₀
      (freeDeltaFrobeniusCoordinateIdeal p σ s)).toLinearEquiv

/-- L/(p,z)からL/(p,φ(z))への具体的な実剰余Frobenius射。 -/
def freeDeltaFrobeniusCoordinateResidueMap (s : σ) :
    (L₀ ⧸ Ideal.span {(p : L₀), MvPolynomial.X (s, 0)}) →+*
      (L₀ ⧸ Ideal.span {(p : L₀), freeDeltaFrobenius p σ (MvPolynomial.X (s, 0))}) :=
  (freeDeltaFrobeniusCoordinateTargetEquiv p σ s).symm.toRingHom.comp
    ((algebraMap (R₀ ⧸ freeDeltaFrobeniusCoordinateIdeal p σ s)
      (B₀ ⧸ freeDeltaFrobeniusCoordinateTargetIdeal p σ s)).comp
      (freeDeltaPairModPEquiv p σ (MvPolynomial.X (s, 0))).toRingHom)

omit [Fact p.Prime] in
/-- 実剰余射は元の自由環のFrobeniusによる標準商射そのもの。 -/
theorem freeDeltaFrobeniusCoordinateResidueMap_mk (s : σ) (y : L₀) :
    freeDeltaFrobeniusCoordinateResidueMap p σ s (Ideal.Quotient.mk _ y) =
      Ideal.Quotient.mk _ (freeDeltaFrobenius p σ y) := by
  apply (freeDeltaFrobeniusCoordinateTargetEquiv p σ s).injective
  change (freeDeltaFrobeniusCoordinateTargetEquiv p σ s)
    ((freeDeltaFrobeniusCoordinateTargetEquiv p σ s).symm _) = _
  rw [RingEquiv.apply_symm_apply]
  change algebraMap (R₀ ⧸ freeDeltaFrobeniusCoordinateIdeal p σ s)
    (B₀ ⧸ freeDeltaFrobeniusCoordinateTargetIdeal p σ s)
    (freeDeltaPairModPEquiv p σ (MvPolynomial.X (s, 0)) (Ideal.Quotient.mk _ y)) = _
  rw [freeDeltaPairModPEquiv_mk, freeDeltaFrobeniusCoordinateTargetEquiv_mk]
  rfl

/-- 実通常射L/(p,z)→L/(p,φ(z))は忠実平坦。 -/
theorem freeDeltaFrobeniusCoordinateResidueMap_faithfullyFlat (s : σ) :
    (freeDeltaFrobeniusCoordinateResidueMap p σ s).FaithfullyFlat := by
  have hb : (algebraMap (R₀ ⧸ freeDeltaFrobeniusCoordinateIdeal p σ s)
      (B₀ ⧸ freeDeltaFrobeniusCoordinateTargetIdeal p σ s)).FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr
      (freeDeltaFrobeniusCoordinateQuotient_moduleFaithfullyFlat p σ s)
  have hs := RingHom.FaithfullyFlat.of_bijective
    (f := (freeDeltaPairModPEquiv p σ (MvPolynomial.X (s, 0))).toRingHom)
    (freeDeltaPairModPEquiv p σ (MvPolynomial.X (s, 0))).bijective
  have ht := RingHom.FaithfullyFlat.of_bijective
    (f := (freeDeltaFrobeniusCoordinateTargetEquiv p σ s).symm.toRingHom)
    (freeDeltaFrobeniusCoordinateTargetEquiv p σ s).symm.bijective
  exact RingHom.FaithfullyFlat.stableUnderComposition _ _
    (RingHom.FaithfullyFlat.stableUnderComposition _ _ hs hb) ht

/-- 指定変数のFrobeniusのmod p像はzのp乗。 -/
theorem freeDeltaFrobeniusCoordinate_mod_p (s : σ) :
    Ideal.Quotient.mk (Ideal.span {(p : L₀)})
      (freeDeltaFrobenius p σ (MvPolynomial.X (s, 0))) =
      Ideal.Quotient.mk (Ideal.span {(p : L₀)}) (MvPolynomial.X (s, 0)) ^ p :=
  freeDeltaFrobenius_mod_p p σ _

end SerrePositivity.BhattScholze
