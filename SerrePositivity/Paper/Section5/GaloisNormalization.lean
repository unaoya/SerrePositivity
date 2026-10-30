module

public import SerrePositivity.CommutativeAlgebra.GaloisNormalization
public import SerrePositivity.CommutativeAlgebra.RegularLocalRing.Normality
public import SerrePositivity.CommutativeAlgebra.Length.CommonResidueField
public import SerrePositivity.CommutativeAlgebra.RegularLocalRing.Basic
public import SerrePositivity.Paper.Section2.Lemma2_2

/-!
# 正規化基底と群作用付き拡大の同時構成

完備局所整域に補題2.2を適用して正則な基底を選び、その基底を保ったままガロア閉包へ上げる。
新しい整域の自己同型群の不変環は選んだ基底に一致する。
有限性・完備性・剰余体の一致を構成し、冪級数環と Witt 冪級数環の表示も新しい剰余体へ移す。
引用への依存は補題2.2の正規化に残る。正則パラメータの正則性は証明済み。
-/

@[expose] public section

universe u v

namespace SerrePositivity.Section5

open IsLocalRing

set_option synthInstance.maxSize 2048

/-- 係数環の同型を形式的冪級数へ係数ごとに適用する。変数は保つ。 -/
private def powerSeriesMapEquiv {k l : Type u} [CommRing k] [CommRing l]
    (σ : Type v) (e : k ≃+* l) : MvPowerSeries σ k ≃+* MvPowerSeries σ l where
  __ := MvPowerSeries.map e.toRingHom
  invFun := MvPowerSeries.map e.symm.toRingHom
  left_inv f := by ext n; simp
  right_inv f := by ext n; simp

/-- 剰余体の同型を Witt ベクトル環の同型へ移す。 -/
private noncomputable def wittMapEquiv {k l : Type u} [CommRing k] [CommRing l]
    (p : ℕ) [Fact p.Prime] (e : k ≃+* l) : WittVector p k ≃+* WittVector p l :=
  RingEquiv.ofBijective (WittVector.map e.toRingHom)
    ⟨WittVector.map_injective _ e.injective, WittVector.map_surjective _ e.surjective⟩

/-- 完備局所整域から、正規化基底とそれを固定する有限群作用付き拡大を同時に選ぶ。
基底は先に補題2.2で選び、ガロア閉包の後で選び直さない。
返す具体的な基底表示は拡大後の剰余体を係数とするので、定理2.5へ直接渡せる。 -/
theorem exists_regular_galoisNormalization
    (D : Type u) [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [IsDomain D]
    [IsAdicComplete (maximalIdeal D) D] [IsAlgClosed (ResidueField D)]
    {h : ℕ} (hdim : ringKrullDim D = h) (hpos : 0 < h)
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField D) p] :
    ∃ (A B : Type u) (_ : CommRing A) (_ : IsRegularLocalRing A)
      (_ : IsAdicComplete (maximalIdeal A) A)
      (_ : CommRing B) (_ : IsDomain B) (_ : IsLocalRing B)
      (_ : IsAdicComplete (maximalIdeal B) B) (_ : Algebra A B) (_ : Algebra D B),
      Module.Finite A B ∧ Module.Finite D B ∧
      Function.Injective (algebraMap A B) ∧ Function.Injective (algebraMap D B) ∧
      Function.Surjective ((residue B).comp (algebraMap A B)) ∧
      Function.Surjective ((residue B).comp (algebraMap D B)) ∧
      (∀ b : B, ((minpoly A b).map (algebraMap A (FractionRing A))).Separable) ∧
      Finite (B ≃ₐ[A] B) ∧
      (∀ b : B, (∀ g : B ≃ₐ[A] B, g b = b) → b ∈ Set.range (algebraMap A B)) ∧
      ringKrullDim A = h ∧
      ∃ t : Fin h → A, Ideal.span (Set.range t) = maximalIdeal A ∧
        ((CharP B p ∧ ∃ f : A ≃+* MvPowerSeries (Fin h) (ResidueField B),
            ∀ j, f (t j) = MvPowerSeries.X j) ∨
         (CharZero B ∧ t ⟨0, hpos⟩ = (p : A) ∧
            ∃ f : A ≃+* MvPowerSeries {j : Fin h // (j : ℕ) ≠ 0}
                (WittVector p (ResidueField B)),
              ∀ (j : Fin h) (hj : (j : ℕ) ≠ 0), f (t j) = MvPowerSeries.X ⟨j, hj⟩)) := by
  obtain ⟨A, aRing, aReg, aComplete, aAlg, hinj, hfinite, hsep, hres,
      hdimA, t, ht, _, hbase⟩ := Section2.lemma_2_2 D hdim hpos p
  let : IsDomain A := isDomain_of_isRegularLocalRing A
  let : IsIntegrallyClosed A := isIntegrallyClosed_of_isRegularLocalRing A
  let er := residueFieldEquiv_of_surjective D hres
  let : IsAlgClosed (ResidueField A) := IsAlgClosed.of_ringEquiv _ _ er.symm
  obtain ⟨B, bRing, bDomain, bLocal, bComplete, abAlg, dbAlg, adbTower,
      hAB, hDB, hinjDB, hresAB, hsepB, hG, hfix⟩ :=
    exists_galoisNormalization_of_normal_base A D hinj hsep
  let := hDB
  have hresDB := residue_surjective_of_finite_of_isAlgClosed D B
  let eDB := residueFieldEquiv_of_surjective B hresDB
  have hinjAB : Function.Injective (algebraMap A B) := by
    rw [IsScalarTower.algebraMap_eq A D B]
    exact hinjDB.comp hinj
  refine ⟨A, B, aRing, aReg, aComplete, bRing, bDomain, bLocal, bComplete, abAlg, dbAlg,
    hAB, hDB, hinjAB, hinjDB, hresAB, hresDB, hsepB, hG, hfix, hdimA, t, ht, ?_⟩
  rcases hbase with ⟨hpD, f, hf⟩ | ⟨hzeroD, htp, f, hf⟩
  · let := hpD
    refine Or.inl ⟨charP_of_injective_algebraMap hinjDB p,
      f.trans (powerSeriesMapEquiv (Fin h) eDB), ?_⟩
    intro j
    change MvPowerSeries.map eDB.toRingHom (f (t j)) = _
    rw [hf, MvPowerSeries.map_X]
  · let := hzeroD
    refine Or.inr ⟨charZero_of_injective_algebraMap hinjDB, htp,
      f.trans (powerSeriesMapEquiv _ (wittMapEquiv p eDB)), ?_⟩
    intro j hj
    change MvPowerSeries.map (wittMapEquiv p eDB).toRingHom (f (t j)) = _
    rw [hf j hj, MvPowerSeries.map_X]

end SerrePositivity.Section5
