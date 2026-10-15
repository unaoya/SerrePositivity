module

public import SerrePositivity.BhattScholze.PrincipalDPBaseChange
public import SerrePositivity.BhattScholze.RankOneDPBaseChangeUniversal

/-! # 一元分冪表示環の任意係数への実基底変更

係数環のpねじれを制限しない。既存の仮定付きAPIは変更しない。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- 任意係数への実基底変更で、拡大した表示関係イデアルが標的の関係イデアルに一致する。 -/
theorem principalDPBaseChangeUniversal_relationIdeal (y : A) :
    principalDPRelationIdeal (algebraMap A B y) =
      ((principalDPRelationIdeal y).map
        (Algebra.TensorProduct.includeRight (R := A) (A := B)).toRingHom).map
          (rankOneDPBaseChangeUniversalEquiv (A := A) (B := B)).toRingHom := by
  rw [Ideal.map_map]
  simp only [principalDPRelationIdeal, Ideal.map_span, Set.image_singleton]
  congr 1
  congr 1
  exact (rankOneDPBaseChangeMap_relation (B := B) y).symm

/-- 一元分冪表示環の、任意の可換係数環への実テンソル基底変更同型。 -/
def principalDPBaseChangeUniversalEquiv (y : A) :
    B ⊗[A] PrincipalDPPresentation A y ≃ₐ[B]
      PrincipalDPPresentation B (algebraMap A B y) :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := A) B (DividedPowerAlgebra A A) B
    (principalDPRelationIdeal y)).trans
    (Ideal.quotientEquivAlg _ _ rankOneDPBaseChangeUniversalEquiv
      (principalDPBaseChangeUniversal_relationIdeal (B := B) y))

/-- 一般基底変更同型はBの係数を保つ。 -/
theorem principalDPBaseChangeUniversalEquiv_coeff (y : A) (b : B) :
    principalDPBaseChangeUniversalEquiv (A := A) y
      (b ⊗ₜ[A] (1 : PrincipalDPPresentation A y)) =
      algebraMap B (PrincipalDPPresentation B (algebraMap A B y)) b :=
  (principalDPBaseChangeUniversalEquiv y).commutes b

/-- 一般基底変更同型の全標準生成元の純テンソル上の式。 -/
theorem principalDPBaseChangeUniversalEquiv_tmul_generator (y : A) (b : B) (n : ℕ) :
    principalDPBaseChangeUniversalEquiv y (b ⊗ₜ[A] principalDPGenerator y n) =
      algebraMap B (PrincipalDPPresentation B (algebraMap A B y)) b *
        principalDPGenerator (algebraMap A B y) n := by
  dsimp only [principalDPBaseChangeUniversalEquiv, principalDPGenerator]
  rw [AlgEquiv.trans_apply, Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul]
  change Ideal.Quotient.mk (principalDPRelationIdeal (algebraMap A B y))
    (rankOneDPBaseChangeUniversalEquiv
      (b ⊗ₜ[A] DividedPowerAlgebra.dp A n (1 : A))) = _
  rw [rankOneDPBaseChangeUniversalEquiv_tmul, DividedPowerAlgebra.map_apply_dp]
  simp only [Algebra.linearMap_apply, map_one, map_mul]
  rfl

end SerrePositivity.BhattScholze
