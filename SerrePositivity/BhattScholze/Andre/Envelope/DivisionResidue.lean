module

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

/-! ## 既存δ除算添加環のraw (p,d)商の具体的表示 -/

@[expose] public noncomputable section DeltaAdjoinDivisionResiduePresentation

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (d : A) (a : σ → A)

/-- raw δ除算添加環における(p,基底dの像)の通常イデアル。 -/
def deltaAdjoinDivisionResidueIdeal : Ideal (DeltaAdjoinDivision D d a) :=
  Ideal.span {(p : DeltaAdjoinDivision D d a), deltaAdjoinDivisionMap D d a d}

/-- raw除算添加環の(p,d)商。ねじれ除去後のadic idealとは別の段階。 -/
abbrev DeltaAdjoinDivisionResidue :=
  DeltaAdjoinDivision D d a ⧸ deltaAdjoinDivisionResidueIdeal D d a

/-- raw環の残余イデアルは、無限自由環の(p,Cd)の標準商射による像。 -/
theorem deltaAdjoinDivisionResidueIdeal_eq_map :
    deltaAdjoinDivisionResidueIdeal D d a =
      Ideal.map (Ideal.Quotient.mk ((relativeFreeDeltaStructure σ D).deltaClosure
        (deltaDivisionRelationIdeal d a)))
        (Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d}) := by
  rw [Ideal.map_span]
  simp only [Set.image_pair, map_natCast]
  rfl

/-- raw添加環の(p,d)商は、無限自由環で(p,Cd)とδ閉包を同時に課した商。 -/
def deltaAdjoinDivisionResidueSupEquiv :
    DeltaAdjoinDivisionResidue D d a ≃+*
      (RelativeFreeDeltaRing (R := A) σ ⧸
        (Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ⊔
          (relativeFreeDeltaStructure σ D).deltaClosure (deltaDivisionRelationIdeal d a))) :=
  (Ideal.quotEquivOfEq (deltaAdjoinDivisionResidueIdeal_eq_map D d a)).trans
    ((DoubleQuot.quotQuotEquivQuotSup
      ((relativeFreeDeltaStructure σ D).deltaClosure (deltaDivisionRelationIdeal d a))
      (Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d})).trans
      (Ideal.quotEquivOfEq (sup_comm _ _)))

/-- 二重商表示同型は元の無限自由環の標準像を同時商の標準像に送る。 -/
theorem deltaAdjoinDivisionResidueSupEquiv_mk (f : RelativeFreeDeltaRing (R := A) σ) :
    deltaAdjoinDivisionResidueSupEquiv D d a
      (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ f)) = Ideal.Quotient.mk _ f := by
  rw [deltaAdjoinDivisionResidueSupEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingEquiv.trans_apply]
  change (Ideal.quotEquivOfEq (sup_comm _ _))
    (DoubleQuot.quotQuotEquivQuotSup
      ((relativeFreeDeltaStructure σ D).deltaClosure (deltaDivisionRelationIdeal d a))
      (Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d})
      (DoubleQuot.quotQuotMk
        ((relativeFreeDeltaStructure σ D).deltaClosure (deltaDivisionRelationIdeal d a))
        (Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d}) f)) = _
  rw [DoubleQuot.quotQuotEquivQuotSup_quotQuotMk, Ideal.quotEquivOfEq_mk]

/-- 基底係数上での二重商比較の標準写像図式。 -/
theorem deltaAdjoinDivisionResidueSupEquiv_coeff (b : A) :
    deltaAdjoinDivisionResidueSupEquiv D d a
      (Ideal.Quotient.mk _ (deltaAdjoinDivisionMap D d a b)) =
      Ideal.Quotient.mk _ (MvPolynomial.C b) :=
  deltaAdjoinDivisionResidueSupEquiv_mk D d a (MvPolynomial.C b)

end SerrePositivity.BhattScholze

end DeltaAdjoinDivisionResiduePresentation

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
    DeltaAdjoinDivisionResidue D d a ≃+* DeltaDivisionFiniteNormalizedDirectLimit D d a u :=
  (deltaAdjoinDivisionResidueSupEquiv D d a).trans
    (deltaDivision_mod_pd_deltaClosure_directLimitEquiv D hpA hpL hg d a u hu)

/-- raw残余商の全段表示は元の基底係数の標準商像に両立する。 -/
theorem deltaAdjoinDivisionResidueDirectLimitEquiv_coeff (b : A) :
    deltaAdjoinDivisionResidueDirectLimitEquiv D hpA hpL hg d a u hu
      (Ideal.Quotient.mk _ (deltaAdjoinDivisionMap D d a b)) =
      deltaDivisionFiniteNormalizedDirectLimitBaseMap D d a u (Ideal.Quotient.mk _ b) := by
  rw [deltaAdjoinDivisionResidueDirectLimitEquiv, RingEquiv.trans_apply,
    deltaAdjoinDivisionResidueSupEquiv_coeff, deltaDivision_mod_pd_deltaClosure_directLimitEquiv_C]

/-- 適切な共通係数商から既存添加環のraw残余商への具体的係数射。 -/
def deltaAdjoinDivisionResidueBaseMap :
    A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a →+* DeltaAdjoinDivisionResidue D d a :=
  (deltaAdjoinDivisionResidueDirectLimitEquiv D hpA hpL hg d a u hu).symm.toRingHom.comp
    (deltaDivisionFiniteNormalizedDirectLimitBaseMap D d a u)

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
    Algebra (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a) (DeltaAdjoinDivisionResidue D d a) :=
  (deltaAdjoinDivisionResidueBaseMap D hpA hpL hg d a u hu).toAlgebra

/-- 既存raw残余商の全段表示は標準係数射に関する代数同型。 -/
def deltaAdjoinDivisionResidueDirectLimitAlgEquiv :
    letI := deltaAdjoinDivisionResidueBaseAlgebra D hpA hpL hg d a u hu
    letI := deltaDivisionFiniteNormalizedDirectLimitBaseAlgebra D d a u
    DeltaAdjoinDivisionResidue D d a ≃ₐ[A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a]
      DeltaDivisionFiniteNormalizedDirectLimit D d a u := by
  letI := deltaAdjoinDivisionResidueBaseAlgebra D hpA hpL hg d a u hu
  letI := deltaDivisionFiniteNormalizedDirectLimitBaseAlgebra D d a u
  apply AlgEquiv.ofRingEquiv
    (f := deltaAdjoinDivisionResidueDirectLimitEquiv D hpA hpL hg d a u hu)
  intro b
  exact (deltaAdjoinDivisionResidueDirectLimitEquiv D hpA hpL hg d a u hu).apply_symm_apply _

/-- 既存添加環のraw (p,d)商は標準係数射によってA/(p,d,a_s)上忠実平坦。 -/
theorem deltaAdjoinDivisionResidue_moduleFaithfullyFlat :
    letI := deltaAdjoinDivisionResidueBaseAlgebra D hpA hpL hg d a u hu
    Module.FaithfullyFlat (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)
      (DeltaAdjoinDivisionResidue D d a) := by
  let := deltaAdjoinDivisionResidueBaseAlgebra D hpA hpL hg d a u hu
  let := deltaDivisionFiniteNormalizedDirectLimitBaseAlgebra D d a u
  let := deltaDivisionFiniteNormalizedDirectLimit_moduleFaithfullyFlat D d a u
  exact Module.FaithfullyFlat.of_linearEquiv _ _
    (deltaAdjoinDivisionResidueDirectLimitAlgEquiv D hpA hpL hg d a u hu).toLinearEquiv

/-- 既存添加環のraw (p,d)商は標準係数射によってA/(p,d,a_s)上平坦。 -/
theorem deltaAdjoinDivisionResidue_moduleFlat :
    letI := deltaAdjoinDivisionResidueBaseAlgebra D hpA hpL hg d a u hu
    Module.Flat (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)
      (DeltaAdjoinDivisionResidue D d a) := by
  let := deltaAdjoinDivisionResidueBaseAlgebra D hpA hpL hg d a u hu
  let := deltaAdjoinDivisionResidue_moduleFaithfullyFlat D hpA hpL hg d a u hu
  infer_instance

end SerrePositivity.BhattScholze

end DeltaAdjoinDivisionResidueFlat

/-! ## 実残余自由δ射の通常テンソルとraw(p,d)商

既存の通常pushout比較と標準テンソル商比較を合成する。
完備化・Tor消滅・対象残余商のδ構造は要求しない。
-/

@[expose] public noncomputable section DeltaDivisionSourceResidueTensor

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (d : A) (c : σ → A)
local notation "P₀" => RelativeFreeDeltaRing (R := A) σ
local notation "I₀" => Ideal.span {(p : P₀), MvPolynomial.C d}
local notation "Q₀" => P₀ ⧸ I₀
local notation "B₀" => DeltaAdjoinDivision D d c
local notation "R₀" => DeltaAdjoinDivisionResidue D d c
local notation "j₀" => deltaAdjoinDivisionMap D d c
local notation "q₀" => Ideal.Quotient.mk
  (DeltaStructure.deltaClosure (relativeFreeDeltaStructure σ D) (deltaDivisionRelationIdeal d c))

/-- 実残余自由δ射による源作用。標準商代数構造を既存のα作用から誘導する。 -/
@[instance_reducible] def deltaDivisionSourceResidueTargetAlgebra : Algebra P₀ Q₀ := by
  letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  letI : Module P₀ P₀ := Algebra.toModule
  infer_instance

/-- 実残余源作用の係数射は、標準商射と自由δ射αの合成そのもの。 -/
theorem deltaDivisionSourceResidueTargetAlgebra_algebraMap :
    letI := deltaDivisionSourceResidueTargetAlgebra (σ := σ) D d
    letI : Module P₀ Q₀ := Algebra.toModule
    algebraMap P₀ Q₀ = (Ideal.Quotient.mk I₀).comp
      (deltaDivisionSourceMap (σ := σ) D d) := rfl

/-- 通常pushout比較の下で、右因子の(p,Cd)イデアルはraw包の実(p,d)イデアルとなる。 -/
theorem deltaDivisionSourceTensor_residueIdeal_map :
    letI := deltaDivisionSourceEvaluationAlgebra D c
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
    letI : Module P₀ P₀ := Algebra.toModule
    ((I₀).map (Algebra.TensorProduct.includeRight (R := P₀) (A := A) (B := P₀)).toRingHom).map
      (deltaDivisionSourceTensorEquiv D d c).toRingHom = deltaAdjoinDivisionResidueIdeal D d c := by
  let := deltaDivisionSourceEvaluationAlgebra D c
  let := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  let : Module P₀ P₀ := Algebra.toModule
  rw [Ideal.map_map]
  have he : (deltaDivisionSourceTensorEquiv D d c).toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := P₀) (A := A) (B := P₀)).toRingHom = q₀ := by
    apply RingHom.ext
    intro r
    change deltaDivisionSourceTensorEquiv D d c (1 ⊗ₜ[P₀] r) = q₀ r
    rw [deltaDivisionSourceTensorEquiv_tmul, map_one, one_mul]
  rw [he]
  exact (deltaAdjoinDivisionResidueIdeal_eq_map D d c).symm

/-- 実残余通常テンソルは、既存rawδ包の実(p,d)商と標準的に環同型。 -/
def deltaDivisionSourceResidueTensorEquiv :
    letI := deltaDivisionSourceEvaluationAlgebra D c
    letI := deltaDivisionSourceResidueTargetAlgebra (σ := σ) D d
    letI : Module P₀ Q₀ := Algebra.toModule
    A ⊗[P₀] Q₀ ≃+* R₀ := by
  letI := deltaDivisionSourceEvaluationAlgebra D c
  letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  letI : Module P₀ P₀ := Algebra.toModule
  letI := deltaDivisionSourceResidueTargetAlgebra (σ := σ) D d
  letI : Module P₀ Q₀ := Algebra.toModule
  exact (Algebra.TensorProduct.tensorQuotientEquiv (R := P₀) A P₀ A I₀).toRingEquiv.trans
    (Ideal.quotientEquiv _ _ (deltaDivisionSourceTensorEquiv D d c)
      (deltaDivisionSourceTensor_residueIdeal_map D d c).symm)

/-- 残余テンソル比較は、各純テンソルを標準基底像と標準商像の積へ送る。 -/
theorem deltaDivisionSourceResidueTensorEquiv_tmul (a : A) (r : P₀) :
    letI := deltaDivisionSourceEvaluationAlgebra D c
    letI := deltaDivisionSourceResidueTargetAlgebra (σ := σ) D d
    letI : Module P₀ Q₀ := Algebra.toModule
    deltaDivisionSourceResidueTensorEquiv D d c (a ⊗ₜ[P₀] Ideal.Quotient.mk I₀ r) =
      Ideal.Quotient.mk (deltaAdjoinDivisionResidueIdeal D d c) (j₀ a * q₀ r) := by
  let := deltaDivisionSourceEvaluationAlgebra D c
  let := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  let : Module P₀ P₀ := Algebra.toModule
  let := deltaDivisionSourceResidueTargetAlgebra (σ := σ) D d
  let : Module P₀ Q₀ := Algebra.toModule
  change Ideal.Quotient.mk (deltaAdjoinDivisionResidueIdeal D d c)
    (deltaDivisionSourceTensorEquiv D d c (a ⊗ₜ[P₀] r)) = _
  rw [deltaDivisionSourceTensorEquiv_tmul]

/-- 実残余テンソル比較は元の係数A作用を保つ。 -/
def deltaDivisionSourceResidueTensorAlgEquiv :
    letI := deltaDivisionSourceEvaluationAlgebra D c
    letI := deltaDivisionSourceResidueTargetAlgebra (σ := σ) D d
    letI : Module P₀ Q₀ := Algebra.toModule
    A ⊗[P₀] Q₀ ≃ₐ[A] R₀ := by
  letI := deltaDivisionSourceEvaluationAlgebra D c
  letI := deltaDivisionSourceResidueTargetAlgebra (σ := σ) D d
  letI : Module P₀ Q₀ := Algebra.toModule
  apply AlgEquiv.ofRingEquiv (f := deltaDivisionSourceResidueTensorEquiv D d c)
  intro a
  change deltaDivisionSourceResidueTensorEquiv D d c (a ⊗ₜ[P₀] 1) =
    Ideal.Quotient.mk (deltaAdjoinDivisionResidueIdeal D d c) (j₀ a)
  have h := deltaDivisionSourceResidueTensorEquiv_tmul D d c a 1
  simpa only [map_one, mul_one] using h

end SerrePositivity.BhattScholze

end DeltaDivisionSourceResidueTensor

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
    (hx : IsSMulRegular (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)
      (Ideal.Quotient.mk (deltaDivisionFirstBaseIdeal (p := p) d a) x)) :
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
    (hx : IsSMulRegular (A ⧸ deltaDivisionFirstBaseIdeal (p := p) (p : A) a)
      (Ideal.Quotient.mk (deltaDivisionFirstBaseIdeal (p := p) (p : A) a) x)) :
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
