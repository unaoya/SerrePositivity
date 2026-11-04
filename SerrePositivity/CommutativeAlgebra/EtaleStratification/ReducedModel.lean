module

public import SerrePositivity.CommutativeAlgebra.EtaleStratification.GenericFactorization
public import SerrePositivity.CommutativeAlgebra.EtaleStratification.GenericLocalization
public import SerrePositivity.CommutativeAlgebra.EtaleStratification.GenericSpread
public import SerrePositivity.CommutativeAlgebra.EtaleStratification.GenericRadicial
public import SerrePositivity.CommutativeAlgebra.EtaleStratification.GenericPrimeSpreading

/-!
# 被約有限代数の一般点の分解の有限モデル

## 概要
一般点での分離部分を有限モデルに戻し、三つの結論それぞれの分母を選ぶ。

## 方針
逆像モデルのエタール性、対角核の nil 性、p 反転後の全射性を別々に延長する。

## 規約
各分母は基底の非零因子。最後に積を取ることで同じ主開集合にそろえられる。

## 使われ方
被約 noetherian 基底における一般点からの延長。
-/

@[expose] public section
noncomputable section
universe u

namespace SerrePositivity.CommutativeAlgebra

open scoped TensorProduct

/-- 一般点の分離部分の有限モデルと、三つの性質を延長する分母。 -/
theorem exists_reduced_generic_model
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsReduced R] [IsReduced S] [Module.Finite R S]
    (p : ℕ) [Fact p.Prime] (hZp : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    ∃ T : Subalgebra R S, Module.Finite R T ∧
      (∃ g : nonZeroDivisors R, Algebra.Etale R (Localization.Away (algebraMap R T g))) ∧
      (∃ g : nonZeroDivisors R,
        (RingHom.ker (Algebra.TensorProduct.lmul' T (S := S)).toRingHom).map
          (algebraMap (S ⊗[T] S) (Localization.Away (algebraMap R (S ⊗[T] S) g))) ≤
            nilradical (Localization.Away (algebraMap R (S ⊗[T] S) g))) ∧
      (∃ g : nonZeroDivisors R, Function.Surjective
        (Localization.awayMap T.val.toRingHom (algebraMap R T g * p))) := by
  let : Algebra R (GenericProduct R) := (genericProductMap R).toAlgebra
  let K := GenericProduct R
  let M := nonZeroDivisors R
  let : IsLocalization M K := isLocalization_genericProduct R
  let A := K ⊗[R] S
  let : Algebra S A := Algebra.TensorProduct.rightAlgebra
  let B := A ⧸ nilradical A
  let f := IsScalarTower.toAlgHom R S B
  let : IsLocalizedModule M f.toLinearMap := isLocalizedModule_genericReducedFiber R S
  let : IsLocalization (Algebra.algebraMapSubmonoid S M) B :=
    isLocalizedModule_iff_isLocalization.mp inferInstance
  obtain ⟨C, hCfinite, hCetale, hCU, hCp⟩ := exists_generic_etale_subalgebra R S p hZp
  let : Module.Finite K C := hCfinite
  let : Algebra.Etale K C := hCetale
  let T := genericSubalgebraModel f C
  let t := genericSubalgebraModelMap f C
  let : Module.Finite R T := genericSubalgebraModel_finite f C
  let : Algebra T C := t.toRingHom.toAlgebra
  let : IsScalarTower R T C := IsScalarTower.of_algebraMap_eq fun r ↦ (t.commutes r).symm
  let : IsScalarTower T C B := IsScalarTower.of_algebraMap_eq fun x ↦ rfl
  let : IsLocalizedModule M t.toLinearMap := genericSubalgebraModel_isLocalizedModule M f C
  let : IsLocalization (Algebra.algebraMapSubmonoid T M) C :=
    isLocalizedModule_iff_isLocalization.mp (show IsLocalizedModule M
      (IsScalarTower.toAlgHom R T C).toLinearMap from
        inferInstanceAs (IsLocalizedModule M t.toLinearMap))
  let : Module.Finite T S := Module.Finite.of_restrictScalars_finite R T S
  let : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  let : IsNoetherianRing (S ⊗[T] S) := IsNoetherianRing.of_finite S (S ⊗[T] S)
  refine ⟨T, inferInstance, exists_away_etale_genericSubalgebraModel M f C, ?_, ?_⟩
  · obtain ⟨g, hg⟩ := exists_away_nil_diagonal_of_localized_fieldMaps R T S B M
      (injective_fieldMaps_of_localization_base (Algebra.algebraMapSubmonoid T M) hCU)
    rw [IsLocalization.ker_map _ _ (Submonoid.map_powers _ _)] at hg
    exact ⟨g, hg⟩
  · apply exists_away_mul_surjective M p t f T.val (C.val.restrictScalars R)
      (by ext; rfl)
    exact (invertPrimeMap_surjective_iff p C.val.toRingHom).mp hCp.surjective

end SerrePositivity.CommutativeAlgebra
