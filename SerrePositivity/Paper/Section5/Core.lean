module

public import SerrePositivity.Paper.Section5.GaloisNormalization
public import SerrePositivity.Paper.Section5.NormalizationPositivity
public import SerrePositivity.CommutativeAlgebra.SupportDimension

/-!
# 完備・代数閉剰余体の場合の核心定理

二つの素イデアル商から正規化基底とガロア拡大を構成し、有限自己同型群の作用を使って
`core_of_normalization_bases` に渡す。長さ代数と比較の抽象論への入口をここで閉じる。
証明は既存の引用入力に依存するが、この接続に新しい未証明入力は必要ない。
-/

public section

universe u

namespace SerrePositivity.Section5

open IsLocalRing

set_option synthInstance.maxSize 2048

/-- 正次元の素イデアル商が固有に交わる核心の場合の正値性。
正規化基底、有限拡大、群作用の選択はすべてこの証明の内部で行う。 -/
theorem core_of_complete_algClosed
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] [IsAlgClosed (ResidueField R)]
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField R) p]
    (P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    (hP : 0 < ringKrullDim (R ⧸ P)) (hQ : 0 < ringKrullDim (R ⧸ Q))
    (hsum : ringKrullDim (R ⧸ P) + ringKrullDim (R ⧸ Q) = ringKrullDim R)
    (hprimary : (P ⊔ Q).radical = maximalIdeal R) :
    0 < chi R (R ⧸ P) (R ⧸ Q) := by
  let : IsLocalRing (R ⧸ P) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  let : IsLocalRing (R ⧸ Q) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk Q) Ideal.Quotient.mk_surjective
  let : IsAdicComplete (maximalIdeal (R ⧸ P)) (R ⧸ P) :=
    isAdicComplete_finite_local_algebra (R := R) (R ⧸ P)
  let : IsAdicComplete (maximalIdeal (R ⧸ Q)) (R ⧸ Q) :=
    isAdicComplete_finite_local_algebra (R := R) (R ⧸ Q)
  let eP := residueFieldEquiv_of_surjective (R ⧸ P)
    (residue_surjective_of_finite_of_isAlgClosed R (R ⧸ P))
  let eQ := residueFieldEquiv_of_surjective (R ⧸ Q)
    (residue_surjective_of_finite_of_isAlgClosed R (R ⧸ Q))
  let : IsAlgClosed (ResidueField (R ⧸ P)) := IsAlgClosed.of_ringEquiv _ _ eP
  let : IsAlgClosed (ResidueField (R ⧸ Q)) := IsAlgClosed.of_ringEquiv _ _ eQ
  let : CharP (ResidueField (R ⧸ P)) p :=
    charP_of_injective_ringHom (f := eP.toRingHom) eP.injective p
  let : CharP (ResidueField (R ⧸ Q)) p :=
    charP_of_injective_ringHom (f := eQ.toRingHom) eQ.injective p
  obtain ⟨h, hPdim⟩ := exists_nat_ringKrullDim_eq (R ⧸ P)
  obtain ⟨e, hQdim⟩ := exists_nat_ringKrullDim_eq (R ⧸ Q)
  have hh : 0 < h := by exact_mod_cast (hPdim ▸ hP)
  have he : 0 < e := by exact_mod_cast (hQdim ▸ hQ)
  obtain ⟨A₀, D, a₀Ring, a₀Reg, a₀Complete, dRing, dDomain, dLocal, dComplete,
      a₀dAlg, pdAlg, hA₀D, hPD, hinjD, hinjPD, hresD, _, hsepD, hG₀, hfixD,
      hdimA₀, t, ht, hbaseD⟩ := exists_regular_galoisNormalization (R ⧸ P) hPdim hh p
  obtain ⟨A, T, aRing, aReg, aComplete, tRing, tDomain, tLocal, tComplete,
      atAlg, qtAlg, hAT, hQT, hinjT, hinjQT, hresT, _, hsepT, hG, hfixT,
      hdimA, a, ha, hbaseT⟩ := exists_regular_galoisNormalization (R ⧸ Q) hQdim he p
  let := hA₀D
  let := hPD
  let := hAT
  let := hQT
  let := hG₀
  let := hG
  let : Algebra R D := ((algebraMap (R ⧸ P) D).comp (algebraMap R (R ⧸ P))).toAlgebra
  let : IsScalarTower R (R ⧸ P) D := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Module.Finite R D := Module.Finite.trans (R ⧸ P) D
  let : Algebra R T := ((algebraMap (R ⧸ Q) T).comp (algebraMap R (R ⧸ Q))).toAlgebra
  let : IsScalarTower R (R ⧸ Q) T := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Module.Finite R T := Module.Finite.trans (R ⧸ Q) T
  exact core_of_normalization_bases p P Q hh he hPdim hQdim hsum hprimary
    D T hinjPD (residue_surjective_of_finite_of_isAlgClosed R D)
    hinjQT (residue_surjective_of_finite_of_isAlgClosed R T)
    A₀ A hinjD hsepD hresD t ht hdimA₀ hinjT hsepT hresT a ha hdimA
    (D ≃ₐ[A₀] D) (T ≃ₐ[A] T) hfixD hfixT hbaseD hbaseT

end SerrePositivity.Section5
