module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.Division.DeltaDivisionFiniteNormalizedPowerEquiv
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! # 有限正規化商の標準一段射の自由性と忠実平坦性 -/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 前段商から次段商への係数射。標準包含との一致は次の公開定理で保証する。 -/
def deltaDivisionFiniteNormalizedStepMap (D : DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) (N : ℕ) :
    DeltaDivisionFiniteNormalizedQuotient D d a u N →+*
      DeltaDivisionFiniteNormalizedQuotient D d a u (N + 1) :=
  (deltaDivisionFiniteNormalizedStepPowerEquiv D d a u N).symm.toRingHom.comp
    (algebraMap (DeltaDivisionFiniteNormalizedQuotient D d a u N)
      (MonicPowerFamilyCover p σ (DeltaDivisionFiniteNormalizedQuotient D d a u N)
        (deltaDivisionFiniteNormalizedStepCoefficients D d a u N)))

/-- 一段射は、有限多項式環の標準包含の商像と一致する。 -/
theorem deltaDivisionFiniteNormalizedStepMap_mk (D : DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) (N : ℕ) (f : MvPolynomial (σ × Fin (N + 1)) A) :
    deltaDivisionFiniteNormalizedStepMap D d a u N (Ideal.Quotient.mk _ f) =
      Ideal.Quotient.mk _ (relativeFreeFiniteStepInclusion N σ f) := by
  apply (deltaDivisionFiniteNormalizedStepPowerEquiv D d a u N).injective
  change (deltaDivisionFiniteNormalizedStepPowerEquiv D d a u N)
    ((deltaDivisionFiniteNormalizedStepPowerEquiv D d a u N).symm _) = _
  rw [RingEquiv.apply_symm_apply, deltaDivisionFiniteNormalizedStepPowerEquiv_inclusion]

/-- 標準一段射による前段商上の次段商の代数構造。 -/
@[instance_reducible] def deltaDivisionFiniteNormalizedStepAlgebra (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) :
    Algebra (DeltaDivisionFiniteNormalizedQuotient D d a u N)
      (DeltaDivisionFiniteNormalizedQuotient D d a u (N + 1)) :=
  (deltaDivisionFiniteNormalizedStepMap D d a u N).toAlgebra

/-- 根添加表示は標準一段射についての前段商代数同型。 -/
def deltaDivisionFiniteNormalizedStepPowerAlgEquiv (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) :
    letI := deltaDivisionFiniteNormalizedStepAlgebra D d a u N
    DeltaDivisionFiniteNormalizedQuotient D d a u (N + 1) ≃ₐ[
      DeltaDivisionFiniteNormalizedQuotient D d a u N]
      MonicPowerFamilyCover p σ (DeltaDivisionFiniteNormalizedQuotient D d a u N)
        (deltaDivisionFiniteNormalizedStepCoefficients D d a u N) := by
  letI := deltaDivisionFiniteNormalizedStepAlgebra D d a u N
  apply AlgEquiv.ofRingEquiv (f := deltaDivisionFiniteNormalizedStepPowerEquiv D d a u N)
  intro b
  exact (deltaDivisionFiniteNormalizedStepPowerEquiv D d a u N).apply_symm_apply _

/-- 標準一段射の次段商は前段商上自由。 -/
theorem deltaDivisionFiniteNormalizedStep_moduleFree (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) :
    let := deltaDivisionFiniteNormalizedStepAlgebra D d a u N
    Module.Free (DeltaDivisionFiniteNormalizedQuotient D d a u N)
      (DeltaDivisionFiniteNormalizedQuotient D d a u (N + 1)) := by
  let := deltaDivisionFiniteNormalizedStepAlgebra D d a u N
  let := monicPowerFamilyCover_moduleFree p σ (DeltaDivisionFiniteNormalizedQuotient D d a u N)
    (deltaDivisionFiniteNormalizedStepCoefficients D d a u N) (Fact.out : p.Prime).pos
  exact Module.Free.of_equiv
    (deltaDivisionFiniteNormalizedStepPowerAlgEquiv D d a u N).symm.toLinearEquiv

/-- 標準一段射の次段商は前段商上平坦。 -/
theorem deltaDivisionFiniteNormalizedStep_moduleFlat (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) :
    let := deltaDivisionFiniteNormalizedStepAlgebra D d a u N
    Module.Flat (DeltaDivisionFiniteNormalizedQuotient D d a u N)
      (DeltaDivisionFiniteNormalizedQuotient D d a u (N + 1)) := by
  let := deltaDivisionFiniteNormalizedStepAlgebra D d a u N
  let := deltaDivisionFiniteNormalizedStep_moduleFree D d a u N
  infer_instance

/-- 標準一段射は忠実平坦。前段商が零環の場合も含む。 -/
theorem deltaDivisionFiniteNormalizedStep_moduleFaithfullyFlat (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) :
    let := deltaDivisionFiniteNormalizedStepAlgebra D d a u N
    Module.FaithfullyFlat (DeltaDivisionFiniteNormalizedQuotient D d a u N)
      (DeltaDivisionFiniteNormalizedQuotient D d a u (N + 1)) := by
  let := deltaDivisionFiniteNormalizedStepAlgebra D d a u N
  let := monicPowerFamilyCover_moduleFaithfullyFlat_all p σ
    (DeltaDivisionFiniteNormalizedQuotient D d a u N)
    (deltaDivisionFiniteNormalizedStepCoefficients D d a u N) (Fact.out : p.Prime).pos
  exact Module.FaithfullyFlat.of_linearEquiv _ _
    (deltaDivisionFiniteNormalizedStepPowerAlgEquiv D d a u N).toLinearEquiv

/-- 標準一段射は単射であり、前段の関係を追加で消さない。 -/
theorem deltaDivisionFiniteNormalizedStepMap_injective (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) :
    Function.Injective (deltaDivisionFiniteNormalizedStepMap D d a u N) := by
  let := deltaDivisionFiniteNormalizedStepAlgebra D d a u N
  let := deltaDivisionFiniteNormalizedStep_moduleFaithfullyFlat D d a u N
  exact FaithfulSMul.algebraMap_injective
    (DeltaDivisionFiniteNormalizedQuotient D d a u N)
    (DeltaDivisionFiniteNormalizedQuotient D d a u (N + 1))

end SerrePositivity.BhattScholze
