module

public import SerrePositivity.CommutativeAlgebra.SystemOfParameters.Finite
public import SerrePositivity.CommutativeAlgebra.SystemOfParameters.Avoidance

/-! # 本文の有限拡大上で使うパラメータの選択

素イデアル回避で `Q` 内の正則列を選び、その像を `R/P` から有限拡大 `D′` へ移す。
有限拡大への移送と正則列の選択はともに証明済み。後者は証明済みの非混合性を使う。
-/

@[expose] public section

universe u

namespace SerrePositivity.Section5

open IsLocalRing

/-- (5.4) のパラメータを、本文の有限拡大 `D′` 上のパラメータ系として選ぶ。 -/
theorem exists_regular_parameters_for_finite_extension
    {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    (D : Type u) [CommRing D] [IsLocalRing D]
    [Algebra R D] [Algebra (R ⧸ P) D] [IsScalarTower R (R ⧸ P) D]
    [Module.Finite (R ⧸ P) D] (hinj : Function.Injective (algebraMap (R ⧸ P) D))
    {h e : ℕ} (hd : ringKrullDim R = (e + h : ℕ))
    (hPdim : ringKrullDim (R ⧸ P) = h) (hQdim : ringKrullDim (R ⧸ Q) = e)
    (hprimary : (P ⊔ Q).radical = maximalIdeal R) :
    ∃ x : Fin h → R, (∀ i, x i ∈ Q) ∧
      RingTheory.Sequence.IsWeaklyRegular R (List.ofFn x) ∧
      IsSystemOfParameters D (algebraMap R D ∘ x) := by
  let : IsLocalRing (R ⧸ P) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  obtain ⟨x, hxQ, hxreg, hxrad⟩ := exists_regular_parameters_in P Q hd hPdim hQdim
    (Nat.add_comm h e) hprimary
  have hx := isSystemOfParameters_quotient_of_radical P x hPdim hxrad
  have hxD := hx.map_finite D hinj
  have hw : algebraMap (R ⧸ P) D ∘ (Ideal.Quotient.mk P ∘ x) =
      algebraMap R D ∘ x := by
    ext i
    exact (IsScalarTower.algebraMap_apply R (R ⧸ P) D (x i)).symm
  rw [hw] at hxD
  exact ⟨x, hxQ, hxreg, hxD⟩

end SerrePositivity.Section5
