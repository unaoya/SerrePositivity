module
public import SerrePositivity.BhattScholze.Delta.Division.AdjoinResidue

public import SerrePositivity.BhattScholze.Andre.Envelope.Normalized
public import SerrePositivity.BhattScholze.Delta.Division.Source
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# 既存 δ 除算包の (p,d) 剰余

## 概要
δ 除算添加環の raw (p,d) 商の具体的表示・標準係数射の忠実平坦性・次の入力の正則性、残余自由 δ 射の通常テンソルと raw (p,d) 商。
BS 著者版 Proposition 3.13 と Remark 7.15 の包の計算に使う、δ 除算包の剰余表示を与える。

## 方針
構成ごとに補題をまとめ、各節で共通の仮定を明示する。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`Envelope/JetRegularity`、`Envelope/MonicCandidate`、`Envelope/MonicSource`、`Envelope/RootRelation`、`Envelope/RootSource`、`PowerRootEnvelope/Unconditional/Residue`、`Variants/ArbitraryFamily`、`Variants/RootedExtension`。
-/

universe u v


/-! ## 既存δ除算添加環のraw (p,d)商の標準係数射と忠実平坦性 -/

@[expose] public noncomputable section DeltaAdjoinDivisionResidueFlat

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A)
variable (hpA : Function.Injective (fun b : A => (p : A) * b))
variable (hpL : Function.Injective (fun f : RelativeFreeDeltaRing (R := A) σ =>
  (p : RelativeFreeDeltaRing (R := A) σ) * f))
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d)

/-- 既存添加環のraw (p,d)商と具体的全段環の環同型。 -/
def deltaAdjoinDivisionResidueDirectLimitEquiv :
    DeltaAdjoinDivisionResidue D d a ≃+* _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedDirectLimit D d a u :=
  (deltaAdjoinDivisionResidueSupEquiv D d a).trans
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivision_mod_pd_deltaClosure_directLimitEquiv D hpA hpL hg d a u hu)

/-- raw残余商の全段表示は元の基底係数の標準商像に両立する。 -/
theorem deltaAdjoinDivisionResidueDirectLimitEquiv_coeff (b : A) :
    deltaAdjoinDivisionResidueDirectLimitEquiv D hpA hpL hg d a u hu
      (Ideal.Quotient.mk _ (deltaAdjoinDivisionMap D d a b)) =
      _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitBaseMap D d a u (Ideal.Quotient.mk _ b) := by
  rw [deltaAdjoinDivisionResidueDirectLimitEquiv, RingEquiv.trans_apply,
    deltaAdjoinDivisionResidueSupEquiv_coeff, _root_.SerrePositivity.BhattScholze.Andre.deltaDivision_mod_pd_deltaClosure_directLimitEquiv_C]

/-- 適切な共通係数商から既存添加環のraw残余商への具体的係数射。 -/
def deltaAdjoinDivisionResidueBaseMap :
    A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a →+* DeltaAdjoinDivisionResidue D d a :=
  (deltaAdjoinDivisionResidueDirectLimitEquiv D hpA hpL hg d a u hu).symm.toRingHom.comp
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitBaseMap D d a u)

/-- raw残余商への係数射は既存deltaAdjoinDivisionMapの標準商像に一致する。 -/
theorem deltaAdjoinDivisionResidueBaseMap_mk (b : A) :
    deltaAdjoinDivisionResidueBaseMap D hpA hpL hg d a u hu (Ideal.Quotient.mk _ b) =
      Ideal.Quotient.mk _ (deltaAdjoinDivisionMap D d a b) := by
  apply (deltaAdjoinDivisionResidueDirectLimitEquiv D hpA hpL hg d a u hu).injective
  change (deltaAdjoinDivisionResidueDirectLimitEquiv D hpA hpL hg d a u hu)
    ((deltaAdjoinDivisionResidueDirectLimitEquiv D hpA hpL hg d a u hu).symm _) = _
  rw [RingEquiv.apply_symm_apply, deltaAdjoinDivisionResidueDirectLimitEquiv_coeff]

/-- 標準係数射による、適切な共通係数商上の既存raw残余商の代数構造。 -/
@[instance_reducible] def deltaAdjoinDivisionResidueBaseAlgebra :
    Algebra (A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a) (DeltaAdjoinDivisionResidue D d a) :=
  (deltaAdjoinDivisionResidueBaseMap D hpA hpL hg d a u hu).toAlgebra

/-- 既存raw残余商の全段表示は標準係数射に関する代数同型。 -/
def deltaAdjoinDivisionResidueDirectLimitAlgEquiv :
    letI := deltaAdjoinDivisionResidueBaseAlgebra D hpA hpL hg d a u hu
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitBaseAlgebra D d a u
    DeltaAdjoinDivisionResidue D d a ≃ₐ[A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a]
      _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedDirectLimit D d a u := by
  letI := deltaAdjoinDivisionResidueBaseAlgebra D hpA hpL hg d a u hu
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitBaseAlgebra D d a u
  apply AlgEquiv.ofRingEquiv
    (f := deltaAdjoinDivisionResidueDirectLimitEquiv D hpA hpL hg d a u hu)
  intro b
  exact (deltaAdjoinDivisionResidueDirectLimitEquiv D hpA hpL hg d a u hu).apply_symm_apply _

/-- 既存添加環のraw (p,d)商は標準係数射によってA/(p,d,a_s)上忠実平坦。 -/
theorem deltaAdjoinDivisionResidue_moduleFaithfullyFlat :
    letI := deltaAdjoinDivisionResidueBaseAlgebra D hpA hpL hg d a u hu
    Module.FaithfullyFlat (A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a)
      (DeltaAdjoinDivisionResidue D d a) := by
  let := deltaAdjoinDivisionResidueBaseAlgebra D hpA hpL hg d a u hu
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitBaseAlgebra D d a u
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimit_moduleFaithfullyFlat D d a u
  exact Module.FaithfullyFlat.of_linearEquiv _ _
    (deltaAdjoinDivisionResidueDirectLimitAlgEquiv D hpA hpL hg d a u hu).toLinearEquiv

/-- 既存添加環のraw (p,d)商は標準係数射によってA/(p,d,a_s)上平坦。 -/
theorem deltaAdjoinDivisionResidue_moduleFlat :
    letI := deltaAdjoinDivisionResidueBaseAlgebra D hpA hpL hg d a u hu
    Module.Flat (A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a)
      (DeltaAdjoinDivisionResidue D d a) := by
  let := deltaAdjoinDivisionResidueBaseAlgebra D hpA hpL hg d a u hu
  let := deltaAdjoinDivisionResidue_moduleFaithfullyFlat D hpA hpL hg d a u hu
  infer_instance

end SerrePositivity.BhattScholze

end DeltaAdjoinDivisionResidueFlat


/-! ## raw除算包の残余商での次入力の正則性

既存の残余商の平坦性を使う。一般のraw環のp正則性は結論しない。
-/

@[expose] public noncomputable section DeltaAdjoinDivisionResidueRegular

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 適切な係数商で正則な元の像は、任意元族のraw(p,d)残余商でも正則。 -/
theorem deltaAdjoinDivisionResidue_isSMulRegular
    (D : DeltaStructure p A)
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (d : A) (a : σ → A) (w : Aˣ) (hw : (w : A) = D.delta d) (x : A)
    (hx : IsSMulRegular (A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a)
      (Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a) x)) :
    IsSMulRegular (DeltaAdjoinDivisionResidue D d a)
      (Ideal.Quotient.mk (deltaAdjoinDivisionResidueIdeal D d a)
        (deltaAdjoinDivisionMap D d a x)) := by
  let L := RelativeFreeDeltaRing (R := A) σ
  have hpL : Function.Injective (fun t : L ↦ (p : L) * t) := by
    have h := (show IsSMulRegular A (p : A) from hpA).of_flat (S := L)
    have h' : IsSMulRegular L (p : L) := by simpa only [map_natCast] using h
    exact h'
  let := deltaAdjoinDivisionResidueBaseAlgebra D hpA hpL hg d a w hw
  let := deltaAdjoinDivisionResidue_moduleFlat D hpA hpL hg d a w hw
  have h := hx.of_flat (S := DeltaAdjoinDivisionResidue D d a)
  change IsSMulRegular (DeltaAdjoinDivisionResidue D d a)
    (deltaAdjoinDivisionResidueBaseMap D hpA hpL hg d a w hw (Ideal.Quotient.mk _ x)) at h
  rw [deltaAdjoinDivisionResidueBaseMap_mk] at h
  exact h

/-- d=pの場合、raw残余イデアルは実際のp主イデアルと一致する。 -/
theorem deltaAdjoinDivisionPResidueIdeal_eq (D : DeltaStructure p A) (a : σ → A) :
    deltaAdjoinDivisionResidueIdeal D (p : A) a =
      Ideal.span {(p : DeltaAdjoinDivision D (p : A) a)} := by
  rw [deltaAdjoinDivisionResidueIdeal, map_natCast]
  exact congrArg Ideal.span
    (Set.insert_eq_of_mem (Set.mem_singleton (p : DeltaAdjoinDivision D (p : A) a)))

/-- raw(p,p)残余商とraw包の実p商との、標準代表元を保つ比較。 -/
def deltaAdjoinDivisionPQuotientResidueEquiv (D : DeltaStructure p A) (a : σ → A) :
    (DeltaAdjoinDivision D (p : A) a ⧸
      Ideal.span {(p : DeltaAdjoinDivision D (p : A) a)}) ≃+*
        DeltaAdjoinDivisionResidue D (p : A) a :=
  Ideal.quotEquivOfEq (deltaAdjoinDivisionPResidueIdeal_eq D a).symm

/-- 比較はすべてのraw包の元の標準商像を保つ。 -/
theorem deltaAdjoinDivisionPQuotientResidueEquiv_mk
    (D : DeltaStructure p A) (a : σ → A) (z : DeltaAdjoinDivision D (p : A) a) :
    deltaAdjoinDivisionPQuotientResidueEquiv D a (Ideal.Quotient.mk _ z) =
      Ideal.Quotient.mk _ z :=
  Ideal.quotEquivOfEq_mk _ _

/-- 適切な係数商で正則な次入力は、任意元族raw p除算包の実mod p商でも正則。 -/
theorem deltaAdjoinDivisionModP_next_isSMulRegular
    (D : DeltaStructure p A)
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (a : σ → A) (w : Aˣ) (hw : (w : A) = D.delta (p : A)) (x : A)
    (hx : IsSMulRegular (A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) (p : A) a)
      (Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) (p : A) a) x)) :
    IsSMulRegular (DeltaAdjoinDivision D (p : A) a ⧸
      Ideal.span {(p : DeltaAdjoinDivision D (p : A) a)})
      (Ideal.Quotient.mk (Ideal.span {(p : DeltaAdjoinDivision D (p : A) a)})
        (deltaAdjoinDivisionMap D (p : A) a x)) := by
  let e := deltaAdjoinDivisionPQuotientResidueEquiv D a
  have hr := deltaAdjoinDivisionResidue_isSMulRegular D hpA hg (p : A) a w hw x hx
  intro z t hzt
  apply e.injective
  apply hr
  change Ideal.Quotient.mk _ (deltaAdjoinDivisionMap D (p : A) a x) * z =
    Ideal.Quotient.mk _ (deltaAdjoinDivisionMap D (p : A) a x) * t at hzt
  have h := congrArg e hzt
  rw [map_mul, map_mul, deltaAdjoinDivisionPQuotientResidueEquiv_mk] at h
  exact h

end SerrePositivity.BhattScholze

end DeltaAdjoinDivisionResidueRegular
