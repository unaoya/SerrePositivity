module

public import SerrePositivity.CommutativeAlgebra.EqualCharacteristicNormalization
public import SerrePositivity.CommutativeAlgebra.FractionRingBasis

/-! # 通常有限正規化の同じ写像を分数体へ延長する

整域の場合の有限性を、係数体・パラメータ・剰余体への写像を保って追加する。
分離性はこの定理に含まれない。部分体族の一般論とはimportを分ける。
-/

@[expose] public noncomputable section
namespace SerrePositivity

/-- 完備局所整域の通常有限正規化と、その同じ写像の有限な分数体延長。
係数・パラメータ・剰余体への写像を保ち、分離性は含めない。 -/
theorem exists_equalCharacteristic_finite_fraction_normalization
    (D : Type*) [CommRing D] [IsDomain D] [IsLocalRing D] [IsNoetherianRing D]
    [IsAdicComplete (IsLocalRing.maximalIdeal D) D] {h : ℕ}
    (hdim : ringKrullDim D = h) (p : ℕ) [Fact p.Prime] [CharP D p] :
    ∃ (φ : IsLocalRing.ResidueField D →+* D) (z : Fin h → D)
      (F : MvPowerSeries (Fin h) (IsLocalRing.ResidueField D) →+* D)
      (hF : Function.Injective F),
      (IsLocalRing.residue D).comp φ = RingHom.id (IsLocalRing.ResidueField D) ∧
        IsSystemOfParameters D z ∧ F.Finite ∧
          Function.Surjective ((IsLocalRing.residue D).comp F) ∧
            (∀ a, F (MvPowerSeries.C a) = φ a) ∧
              (∀ i, F (MvPowerSeries.X i) = z i) ∧ (fractionRingMap F hF).Finite := by
  obtain ⟨φ, z, F, hφ, hz, hF, hfin, hres, hC, hX⟩ :=
    exists_equalCharacteristic_finite_normalization D hdim p
  exact ⟨φ, z, F, hF, hφ, hz, hfin, hres, hC, hX, fractionRingMap_finite F hF hfin⟩

end SerrePositivity
