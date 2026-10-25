module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.Division.DeltaDivisionFiniteJetStepResolution
public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.Division.DeltaDivisionNormalizedStepResolution

/-! # 元のδ関係段間射と正規化段間射の標準比較

同じ初期N+2変数分離を両側へ使用し、後続変数を保つ係数変更を明示する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A)
variable (hpA : Function.Injective (fun z : A ↦ (p : A) * z))
variable (hpL : Function.Injective (fun z : RelativeFreeDeltaRing (R := A) σ ↦
  (p : RelativeFreeDeltaRing (R := A) σ) * z))
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (d : A) (a : σ → A) (v : Aˣ) (hv : (v : A) = D.delta d) (N : ℕ)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "I₀" => Ideal.span {(p : L₀), MvPolynomial.C d} ⊔
  deltaDivisionFiniteRelationIdeal D d a (N + 1)
local notation "I₁" => Ideal.span {(p : L₀), MvPolynomial.C d} ⊔
  deltaDivisionFiniteRelationIdeal D d a (N + 2)
local notation "J₁" => deltaDivisionFirstResidueIdeal D d a ⊔
  deltaDivisionFiniteNormalizedWittIdeal D d a v (N + 1)
local notation "K₁" => deltaDivisionFiniteNormalizedPresentationIdeal D d a v (N + 1)
local notation "S₀" => MvPolynomial (σ × Fin (N + 2)) A ⧸
  deltaDivisionNormalizedStepSourceIdeal D d a v N
local notation "Q₁" => DeltaDivisionFiniteNormalizedQuotient D d a v (N + 1)

include hv in
/-- 全自由環の次段正規化イデアルは同じN+2変数分離で次段係数イデアルへ移る。 -/
theorem deltaDivisionNormalizedAmbientNextIdeal_map_split :
    Ideal.map (relativeFreeFiniteVariableSplitAlgEquiv (N + 2) σ A).toRingHom J₁ =
      (K₁).map (MvPolynomial.C : MvPolynomial (σ × Fin (N + 2)) A →+*
        MvPolynomial (σ × ℕ) (MvPolynomial (σ × Fin (N + 2)) A)) := by
  rw [← deltaDivisionFiniteNormalizedPresentationIdeal_map_initial D d a v hv (N + 1),
    Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro f
  exact relativeFreeFiniteVariableSplitAlgEquiv_initial (N + 2) σ A f

/-- 全自由環の次段正規化商は次段有限実商上の後続多項式環。 -/
def deltaDivisionNormalizedAmbientNextEquiv :
    (L₀ ⧸ J₁) ≃+* MvPolynomial (σ × ℕ) Q₁ :=
  (Ideal.quotientEquiv _ _ (relativeFreeFiniteVariableSplitAlgEquiv (N + 2) σ A).toRingEquiv
    (deltaDivisionNormalizedAmbientNextIdeal_map_split D d a v hv N).symm).trans
    (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ × ℕ) K₁).symm.toRingEquiv

/-- 次段正規化商の比較は、同じ変数分離後の標準係数商写像。 -/
theorem deltaDivisionNormalizedAmbientNextEquiv_mk (f : L₀) :
    deltaDivisionNormalizedAmbientNextEquiv D d a v hv N (Ideal.Quotient.mk _ f) =
      MvPolynomial.map (Ideal.Quotient.mk K₁)
        (relativeFreeFiniteVariableSplitAlgEquiv (N + 2) σ A f) := by
  rw [deltaDivisionNormalizedAmbientNextEquiv, RingEquiv.trans_apply, Ideal.quotientEquiv_mk]
  change MvPolynomial.eval₂Hom (MvPolynomial.C.comp (Ideal.Quotient.mk K₁)) MvPolynomial.X
    (relativeFreeFiniteVariableSplitAlgEquiv (N + 2) σ A f) =
    MvPolynomial.map (Ideal.Quotient.mk K₁)
      (relativeFreeFiniteVariableSplitAlgEquiv (N + 2) σ A f)
  rw [MvPolynomial.map_eq_eval₂Hom_C_comp]

/-- 元の下位δ関係商を、有限実源商上の後続多項式環へ移す同型。 -/
def deltaDivisionFiniteJetStepSourceEquiv :
    (L₀ ⧸ I₀) ≃+* MvPolynomial (σ × ℕ) S₀ :=
  (deltaDivisionFiniteNormalizedQuotientEquiv D hpA hpL hg d a v hv N).trans
    (deltaDivisionNormalizedAmbientSourceEquiv D d a v N hv)

/-- 元の下位商の比較は、逆Witt座標と標準係数商写像の合成。 -/
theorem deltaDivisionFiniteJetStepSourceEquiv_mk (f : L₀) :
    deltaDivisionFiniteJetStepSourceEquiv D hpA hpL hg d a v hv N (Ideal.Quotient.mk _ f) =
      MvPolynomial.map (Ideal.Quotient.mk (deltaDivisionNormalizedStepSourceIdeal D d a v N))
        (relativeFreeFiniteVariableSplitAlgEquiv (N + 2) σ A
          (relativeFreeWittInverseMap D hpA f)) := by
  rw [deltaDivisionFiniteJetStepSourceEquiv, RingEquiv.trans_apply,
    deltaDivisionFiniteNormalizedQuotientEquiv_mk, deltaDivisionNormalizedAmbientSourceEquiv_mk]

/-- 元の次段δ関係商を、次段有限実商上の後続多項式環へ移す同型。 -/
def deltaDivisionFiniteJetStepTargetEquiv :
    (L₀ ⧸ I₁) ≃+* MvPolynomial (σ × ℕ) Q₁ :=
  (deltaDivisionFiniteNormalizedQuotientEquiv D hpA hpL hg d a v hv (N + 1)).trans
    (deltaDivisionNormalizedAmbientNextEquiv D d a v hv N)

/-- 元の次段商の比較も同じ逆座標・変数分離による標準係数商写像。 -/
theorem deltaDivisionFiniteJetStepTargetEquiv_mk (f : L₀) :
    deltaDivisionFiniteJetStepTargetEquiv D hpA hpL hg d a v hv N (Ideal.Quotient.mk _ f) =
      MvPolynomial.map (Ideal.Quotient.mk K₁)
        (relativeFreeFiniteVariableSplitAlgEquiv (N + 2) σ A
          (relativeFreeWittInverseMap D hpA f)) := by
  rw [deltaDivisionFiniteJetStepTargetEquiv, RingEquiv.trans_apply,
    deltaDivisionFiniteNormalizedQuotientEquiv_mk, deltaDivisionNormalizedAmbientNextEquiv_mk]

/-- 元の段間標準射は、正規化側標準射の後続多項式係数変更に一致する。 -/
theorem deltaDivisionFiniteJetStepComparison :
    (deltaDivisionFiniteJetStepTargetEquiv D hpA hpL hg d a v hv N).toRingHom.comp
      (deltaDivisionFiniteJetStepMap D d a N) =
    (MvPolynomial.map (deltaDivisionNormalizedStepNextMap D d a v N)).comp
      (deltaDivisionFiniteJetStepSourceEquiv D hpA hpL hg d a v hv N).toRingHom := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro f
  change deltaDivisionFiniteJetStepTargetEquiv D hpA hpL hg d a v hv N
    (deltaDivisionFiniteJetStepMap D d a N (Ideal.Quotient.mk _ f)) =
    MvPolynomial.map (deltaDivisionNormalizedStepNextMap D d a v N)
      (deltaDivisionFiniteJetStepSourceEquiv D hpA hpL hg d a v hv N (Ideal.Quotient.mk _ f))
  rw [deltaDivisionFiniteJetStepMap_mk, deltaDivisionFiniteJetStepTargetEquiv_mk,
    deltaDivisionFiniteJetStepSourceEquiv_mk, MvPolynomial.map_map]
  have hc : (deltaDivisionNormalizedStepNextMap D d a v N).comp
      (Ideal.Quotient.mk (deltaDivisionNormalizedStepSourceIdeal D d a v N)) =
      Ideal.Quotient.mk K₁ := by
    apply RingHom.ext
    intro z
    exact deltaDivisionNormalizedStepNextMap_mk D d a v N z
  rw [hc]

end SerrePositivity.BhattScholze
