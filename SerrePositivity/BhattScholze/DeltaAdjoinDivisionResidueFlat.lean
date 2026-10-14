module

public import SerrePositivity.BhattScholze.DeltaAdjoinDivisionResiduePresentation

/-! # 既存δ除算添加環のraw (p,d)商の標準係数射と忠実平坦性 -/

@[expose] public noncomputable section
universe u v
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
