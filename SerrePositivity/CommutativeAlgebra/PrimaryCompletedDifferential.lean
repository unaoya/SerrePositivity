module

public import SerrePositivity.CommutativeAlgebra.CompletedKaehlerFinite
public import SerrePositivity.CommutativeAlgebra.CompletedDifferentialTransitivity
public import SerrePositivity.CommutativeAlgebra.EqualCharacteristicNormalization

/-! # 準素なパラメータに対する完備微分の有限生成性

指定剰余写像から閉ファイバーの有限性を供給し、完備微分の有限生成判定へ適用する。
既存の通常の有限正規化が与える同じ係数写像・パラメータにも接続する。
分数体拡大の分離性は主張しない。
-/

@[expose] public section
universe u
namespace SerrePositivity
open IsLocalRing

/-- 共通の剰余体と準素性から、パラメータイデアルに沿う完備微分の有限性を得る。 -/
theorem moduleFinite_completedKaehler_of_primary_common_residue
    {k S : Type u} [CommRing k] [CommRing S] [Algebra k S]
    [IsNoetherianRing S] [IsLocalRing S] [IsAdicComplete (maximalIdeal S) S]
    (hres : Function.Surjective ((residue S).comp (algebraMap k S)))
    (I : Ideal S) (hI : I.radical = maximalIdeal S) :
    Module.Finite S (AdicCompletion I (KaehlerDifferential k S)) := by
  have hIm : I ≤ maximalIdeal S := by rw [← hI]; exact Ideal.le_radical
  let : IsAdicComplete I S := isAdicComplete_finite_of_le_maximalIdeal I hIm
  let : Module.Finite k (S ⧸ I) := finite_quotient_of_common_residue_primary hres I hI
  exact moduleFinite_completedKaehler_of_finiteType_fiber I I.fg_of_isNoetherianRing

/-- 有限型の閉ファイバーを実際に確認すると、完備した推移列の像と核が一致する。 -/
theorem range_completedDifferentialBaseChange_eq_ker_of_finiteType_fiber
    {k R S : Type*} [CommRing k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra R S] [Algebra k S] [IsScalarTower k R S]
    [Algebra.EssFiniteType R S] [IsNoetherianRing S] [IsLocalRing S]
    (I : Ideal S) (hI : I ≤ maximalIdeal S) [IsAdicComplete I S]
    [Algebra.EssFiniteType k (S ⧸ I)] :
    LinearMap.range (completedDifferentialBaseChange (R := R) I k) =
      LinearMap.ker (completedDifferentialRestriction (R := R) I hI k) := by
  let : Module.Finite S (AdicCompletion I (KaehlerDifferential k S)) :=
    moduleFinite_completedKaehler_of_finiteType_fiber I I.fg_of_isNoetherianRing
  exact range_completedDifferentialBaseChange_eq_ker I hI k

/-- 通常の有限正規化に、同じ係数写像・パラメータでの完備微分の有限性を添える。 -/
theorem exists_equalCharacteristic_normalization_with_finite_differential
    (D : Type u) [CommRing D] [IsLocalRing D] [IsNoetherianRing D]
    [IsAdicComplete (maximalIdeal D) D] {h : ℕ} (hdim : ringKrullDim D = h)
    (p : ℕ) [Fact p.Prime] [CharP D p] :
    ∃ (φ : ResidueField D →+* D) (z : Fin h → D)
      (F : MvPowerSeries (Fin h) (ResidueField D) →+* D),
      (residue D).comp φ = RingHom.id (ResidueField D) ∧
        IsSystemOfParameters D z ∧ Function.Injective F ∧ F.Finite ∧
          Function.Surjective ((residue D).comp F) ∧
            (∀ a, F (MvPowerSeries.C a) = φ a) ∧ (∀ i, F (MvPowerSeries.X i) = z i) ∧
              (let _ : Algebra (ResidueField D) D := φ.toAlgebra
               Module.Finite D (AdicCompletion (Ideal.span (Set.range z))
                 (KaehlerDifferential (ResidueField D) D))) := by
  obtain ⟨φ, z, F, hφ, hz, hinj, hfin, hres, hC, hX⟩ :=
    exists_equalCharacteristic_finite_normalization D hdim p
  refine ⟨φ, z, F, hφ, hz, hinj, hfin, hres, hC, hX, ?_⟩
  let : Algebra (ResidueField D) D := φ.toAlgebra
  have hφsurj : Function.Surjective ((residue D).comp (algebraMap (ResidueField D) D)) := by
    change Function.Surjective ((residue D).comp φ)
    rw [hφ]
    exact Function.surjective_id
  exact moduleFinite_completedKaehler_of_primary_common_residue hφsurj
    (Ideal.span (Set.range z)) hz.2

end SerrePositivity
