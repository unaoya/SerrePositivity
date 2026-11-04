module

public import SerrePositivity.CommutativeAlgebra.EtaleStratification.GenericModel
public import SerrePositivity.CommutativeAlgebra.EtaleStratification.GenericPoints

/-!
# 被約な一般ファイバーの局所化構造

## 概要
被約代数の一般ファイバーを被約化しても、元の代数の局所化である。

## 方針
局所化では nilradical が像に移るため、被約環の局所化は被約。
零核の商写像を用いて局所化構造を移す。

## 規約
基底の全商環と、代数の中で反転する基底由来の元を区別する。

## 使われ方
一般点上の有限エタール部分代数の逆像を有限モデルにする。
-/

@[expose] public section
noncomputable section
universe u

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.CommutativeAlgebra

open scoped TensorProduct

/-- 被約環の局所化を被約化しても、同じ乗法集合での局所化。 -/
theorem isLocalization_reduced_localization
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [IsReduced A]
    (M : Submonoid A) [IsLocalization M B] :
    IsLocalization M (B ⧸ nilradical B) := by
  have hn : nilradical B = ⊥ := by
    have h := IsLocalization.map_radical M B (⊥ : Ideal A)
    have hA : (⊥ : Ideal A).radical = ⊥ := nilradical_eq_zero A
    change (⊥ : Ideal B).radical = ⊥
    simpa only [hA, Ideal.map_bot] using h.symm
  have h := IsLocalization.of_surjective M B (RingHom.id A) Function.surjective_id
    (Ideal.Quotient.mk (nilradical B)) Ideal.Quotient.mk_surjective
    (by ext; rfl) (by rw [Ideal.mk_ker, hn]; exact bot_le)
  have hm : M.map (RingHom.id A) = M := by
    ext x
    simp
  rw [hm] at h
  exact h

/-- 被約な有限代数の一般ファイバーへの射は、基底の非零因子による加群の局所化。 -/
theorem isLocalizedModule_genericReducedFiber
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsReduced R] [IsReduced S] :
    letI : Algebra R (GenericProduct R) := (genericProductMap R).toAlgebra
    letI : Module R (GenericProduct R) := Algebra.toModule
    let A := GenericProduct R ⊗[R] S
    letI : Algebra S A := Algebra.TensorProduct.rightAlgebra
    let B := A ⧸ nilradical A
    IsLocalizedModule (nonZeroDivisors R) (IsScalarTower.toAlgHom R S B).toLinearMap := by
  let : Algebra R (GenericProduct R) := (genericProductMap R).toAlgebra
  let : Module R (GenericProduct R) := Algebra.toModule
  let : IsLocalization (nonZeroDivisors R) (GenericProduct R) :=
    isLocalization_genericProduct R
  let A := GenericProduct R ⊗[R] S
  let : Algebra S A := Algebra.TensorProduct.rightAlgebra
  let B := A ⧸ nilradical A
  let : IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) B :=
    isLocalization_reduced_localization S A _
  exact isLocalizedModule_iff_isLocalization.mpr inferInstance

end SerrePositivity.CommutativeAlgebra
