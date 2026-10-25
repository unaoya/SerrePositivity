module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.Division.DeltaDivisionFiniteNormalizedInitialPowerEquiv

/-! # 適切な係数商上の初期有限正規化商の自由性と忠実平坦性 -/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- A/(p,d,a_s)から初期有限正規化商への具体的係数射。 -/
def deltaDivisionFiniteNormalizedInitialBaseMap (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) :
    A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a →+*
      DeltaDivisionFiniteNormalizedQuotient D d a u 0 :=
  (deltaDivisionFiniteNormalizedInitialPowerEquiv D d a u).symm.toRingHom.comp
    (algebraMap (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)
      (DeltaDivisionFirstPowerCover D d a u))

/-- 初期係数射は元の基底係数の標準商像に一致する。 -/
theorem deltaDivisionFiniteNormalizedInitialBaseMap_mk (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (b : A) :
    deltaDivisionFiniteNormalizedInitialBaseMap D d a u (Ideal.Quotient.mk _ b) =
      Ideal.Quotient.mk _ (MvPolynomial.C b) := by
  apply (deltaDivisionFiniteNormalizedInitialPowerEquiv D d a u).injective
  change (deltaDivisionFiniteNormalizedInitialPowerEquiv D d a u)
    ((deltaDivisionFiniteNormalizedInitialPowerEquiv D d a u).symm _) = _
  rw [RingEquiv.apply_symm_apply, deltaDivisionFiniteNormalizedInitialPowerEquiv_C]

/-- 標準係数射による適切な係数商上の初期有限商の代数構造。 -/
@[instance_reducible] def deltaDivisionFiniteNormalizedInitialBaseAlgebra
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :
    Algebra (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)
      (DeltaDivisionFiniteNormalizedQuotient D d a u 0) :=
  (deltaDivisionFiniteNormalizedInitialBaseMap D d a u).toAlgebra

/-- 初期根添加表示は標準係数射に関する代数同型。 -/
def deltaDivisionFiniteNormalizedInitialPowerAlgEquiv (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) :
    letI := deltaDivisionFiniteNormalizedInitialBaseAlgebra D d a u
    DeltaDivisionFiniteNormalizedQuotient D d a u 0 ≃ₐ[
      A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a] DeltaDivisionFirstPowerCover D d a u := by
  letI := deltaDivisionFiniteNormalizedInitialBaseAlgebra D d a u
  apply AlgEquiv.ofRingEquiv (f := deltaDivisionFiniteNormalizedInitialPowerEquiv D d a u)
  intro b
  exact (deltaDivisionFiniteNormalizedInitialPowerEquiv D d a u).apply_symm_apply _

/-- 初期有限正規化商はA/(p,d,a_s)上自由。 -/
theorem deltaDivisionFiniteNormalizedInitial_moduleFree (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) :
    letI := deltaDivisionFiniteNormalizedInitialBaseAlgebra D d a u
    Module.Free (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)
      (DeltaDivisionFiniteNormalizedQuotient D d a u 0) := by
  let := deltaDivisionFiniteNormalizedInitialBaseAlgebra D d a u
  let := monicPowerFamilyCover_moduleFree p σ
    (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)
    (deltaDivisionFirstPowerCoefficients D d a u) (Fact.out : p.Prime).pos
  exact Module.Free.of_equiv
    (deltaDivisionFiniteNormalizedInitialPowerAlgEquiv D d a u).symm.toLinearEquiv

/-- 初期有限正規化商はA/(p,d,a_s)上平坦。 -/
theorem deltaDivisionFiniteNormalizedInitial_moduleFlat (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) :
    letI := deltaDivisionFiniteNormalizedInitialBaseAlgebra D d a u
    Module.Flat (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)
      (DeltaDivisionFiniteNormalizedQuotient D d a u 0) := by
  let := deltaDivisionFiniteNormalizedInitialBaseAlgebra D d a u
  let := deltaDivisionFiniteNormalizedInitial_moduleFree D d a u
  infer_instance

/-- 初期有限正規化商はA/(p,d,a_s)上忠実平坦。零係数商も含む。 -/
theorem deltaDivisionFiniteNormalizedInitial_moduleFaithfullyFlat (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) :
    letI := deltaDivisionFiniteNormalizedInitialBaseAlgebra D d a u
    Module.FaithfullyFlat (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)
      (DeltaDivisionFiniteNormalizedQuotient D d a u 0) := by
  let := deltaDivisionFiniteNormalizedInitialBaseAlgebra D d a u
  let := monicPowerFamilyCover_moduleFaithfullyFlat_all p σ
    (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)
    (deltaDivisionFirstPowerCoefficients D d a u) (Fact.out : p.Prime).pos
  exact Module.FaithfullyFlat.of_linearEquiv _ _
    (deltaDivisionFiniteNormalizedInitialPowerAlgEquiv D d a u).toLinearEquiv

end SerrePositivity.BhattScholze
