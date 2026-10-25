module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.DeltaRoot.DeltaRootRelationCoefficientQuotient

/-! # 根関係の具体的係数商の標準射・自由性・忠実平坦性 -/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (d : A) (b : σ → A)

/-- A/(p,d)から根関係の具体的係数商への標準係数射。 -/
def deltaRootRelationCoefficientBaseMap :
    A ⧸ Ideal.span {(p : A), d} →+* DeltaRootRelationCoefficientQuotient (p := p) d b :=
  (deltaRootRelationCoefficientPowerEquiv (p := p) d b).symm.toRingHom.comp
    (algebraMap (A ⧸ Ideal.span {(p : A), d})
      (MonicPowerFamilyCover p σ (A ⧸ Ideal.span {(p : A), d})
        (fun s => Ideal.Quotient.mk _ (b s))))

omit [Fact p.Prime] in
/-- 標準係数射は元の係数の商像に一致する。 -/
theorem deltaRootRelationCoefficientBaseMap_mk (c : A) :
    deltaRootRelationCoefficientBaseMap (p := p) d b (Ideal.Quotient.mk _ c) =
      Ideal.Quotient.mk _ (MvPolynomial.C c) := by
  apply (deltaRootRelationCoefficientPowerEquiv (p := p) d b).injective
  change (deltaRootRelationCoefficientPowerEquiv (p := p) d b)
    ((deltaRootRelationCoefficientPowerEquiv (p := p) d b).symm _) = _
  rw [RingEquiv.apply_symm_apply, deltaRootRelationCoefficientPowerEquiv_C]

/-- 標準係数射による根関係係数商の代数構造。 -/
@[instance_reducible] def deltaRootRelationCoefficientBaseAlgebra :
    Algebra (A ⧸ Ideal.span {(p : A), d}) (DeltaRootRelationCoefficientQuotient (p := p) d b) :=
  (deltaRootRelationCoefficientBaseMap (p := p) d b).toAlgebra

/-- 根関係の係数商比較は標準係数射に関する代数同型。 -/
def deltaRootRelationCoefficientPowerAlgEquiv :
    letI := deltaRootRelationCoefficientBaseAlgebra (p := p) d b
    DeltaRootRelationCoefficientQuotient (p := p) d b ≃ₐ[A ⧸ Ideal.span {(p : A), d}]
      MonicPowerFamilyCover p σ (A ⧸ Ideal.span {(p : A), d})
        (fun s => Ideal.Quotient.mk _ (b s)) := by
  letI := deltaRootRelationCoefficientBaseAlgebra (p := p) d b
  apply AlgEquiv.ofRingEquiv (f := deltaRootRelationCoefficientPowerEquiv (p := p) d b)
  intro c
  exact (deltaRootRelationCoefficientPowerEquiv (p := p) d b).apply_symm_apply _

/-- 根関係の係数商は標準射によってA/(p,d)上自由。 -/
theorem deltaRootRelationCoefficient_moduleFree :
    letI := deltaRootRelationCoefficientBaseAlgebra (p := p) d b
    Module.Free (A ⧸ Ideal.span {(p : A), d})
      (DeltaRootRelationCoefficientQuotient (p := p) d b) := by
  let := deltaRootRelationCoefficientBaseAlgebra (p := p) d b
  let := monicPowerFamilyCover_moduleFree p σ (A ⧸ Ideal.span {(p : A), d})
    (fun s => Ideal.Quotient.mk _ (b s)) (Fact.out : p.Prime).pos
  exact Module.Free.of_equiv
    (deltaRootRelationCoefficientPowerAlgEquiv (p := p) d b).symm.toLinearEquiv

/-- 根関係の係数商は標準射によってA/(p,d)上忠実平坦。零係数商も含む。 -/
theorem deltaRootRelationCoefficient_moduleFaithfullyFlat :
    letI := deltaRootRelationCoefficientBaseAlgebra (p := p) d b
    Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A), d})
      (DeltaRootRelationCoefficientQuotient (p := p) d b) := by
  let := deltaRootRelationCoefficientBaseAlgebra (p := p) d b
  let := monicPowerFamilyCover_moduleFaithfullyFlat_all p σ (A ⧸ Ideal.span {(p : A), d})
    (fun s => Ideal.Quotient.mk _ (b s)) (Fact.out : p.Prime).pos
  exact Module.FaithfullyFlat.of_linearEquiv _ _
    (deltaRootRelationCoefficientPowerAlgEquiv (p := p) d b).toLinearEquiv

/-- 根関係の係数商は標準射によってA/(p,d)上平坦。 -/
theorem deltaRootRelationCoefficient_moduleFlat :
    letI := deltaRootRelationCoefficientBaseAlgebra (p := p) d b
    Module.Flat (A ⧸ Ideal.span {(p : A), d})
      (DeltaRootRelationCoefficientQuotient (p := p) d b) := by
  let := deltaRootRelationCoefficientBaseAlgebra (p := p) d b
  let := deltaRootRelationCoefficient_moduleFaithfullyFlat (p := p) d b
  infer_instance

omit [Fact p.Prime] in
/-- 係数商内で各変数のp乗は指定した元の標準像に一致する。 -/
theorem deltaRootRelationCoefficient_variable_pow (s : σ) :
    (Ideal.Quotient.mk
      (deltaDivisionFirstBaseIdeal (p := p) (MvPolynomial.C d) (deltaRootRelationFamily (p := p) b))
      (MvPolynomial.X s)) ^ p =
      deltaRootRelationCoefficientBaseMap (p := p) d b (Ideal.Quotient.mk _ (b s)) := by
  apply (deltaRootRelationCoefficientPowerEquiv (p := p) d b).injective
  rw [deltaRootRelationCoefficientBaseMap_mk, map_pow,
    deltaRootRelationCoefficientPowerEquiv_X, deltaRootRelationCoefficientPowerEquiv_C,
    monicPowerFamilyRoot_pow]

end SerrePositivity.BhattScholze
