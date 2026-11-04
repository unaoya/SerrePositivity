module

public import SerrePositivity.CommutativeAlgebra.EtaleStratification.GenericStructure

/-!
# 全商環上の有限エタール部分代数

## 概要
一般点での体ごとの分離部分を、被約な一般ファイバーの部分代数としてまとめる。

## 方針
分離閉包の積から一般ファイバーへの単射の像を取る。
有限エタール性、普遍同相性、p 反転後の同型をこの像へ移す。

## 規約
部分代数の包含そのものについて後半の性質を記述する。

## 使われ方
逆像により有限モデルを作るための一般点上の入力。
-/

@[expose] public section
noncomputable section
universe u

namespace SerrePositivity.CommutativeAlgebra

open scoped TensorProduct

/-- 一般ファイバーの中に、有限エタールな分離部分を選ぶ。 -/
theorem exists_generic_etale_subalgebra
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsReduced R] [Module.Finite R S]
    (p : ℕ) [Fact p.Prime] (hZp : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    letI : Algebra R (GenericProduct R) := (genericProductMap R).toAlgebra
    letI : Module R (GenericProduct R) := Algebra.toModule
    let B := (GenericProduct R ⊗[R] S) ⧸ nilradical (GenericProduct R ⊗[R] S)
    ∃ C : Subalgebra (GenericProduct R) B,
      Module.Finite (GenericProduct R) C ∧ Algebra.Etale (GenericProduct R) C ∧
        IsUniversalHomeomorphism C.val.toRingHom ∧
        Function.Bijective (invertPrimeMap p C.val.toRingHom) := by
  let : Algebra R (GenericProduct R) := (genericProductMap R).toAlgebra
  let : Module R (GenericProduct R) := Algebra.toModule
  let K := GenericProduct R
  let B := (K ⊗[R] S) ⧸ nilradical (K ⊗[R] S)
  obtain ⟨hfinite, _, _, m, v, L, hL, a, ⟨e⟩, hfields⟩ := generic_structure R S p hZp
  let : Finite (GenericPoint R) := hfinite
  let : ∀ j, Field (L j) := hL
  let : ∀ j, Algebra (GenericField (v j)) (L j) := a
  let : Algebra K (∀ j, L j) := (RingHom.pi (fun j ↦
    (algebraMap (GenericField (v j)) (L j)).comp (Pi.evalRingHom GenericField (v j)))).toAlgebra
  let M (j : Fin m) : Type u := separableClosure (GenericField (v j)) (L j)
  let : ∀ j, Module.Finite (GenericField (v j)) (L j) := fun j ↦ (hfields j).1
  let : ∀ j, Module.Finite (GenericField (v j)) (M j) := fun j ↦ (hfields j).2.1
  let : ∀ j, Algebra.Etale (GenericField (v j)) (M j) := fun j ↦ (hfields j).2.2.1
  let : ∀ j, IsPurelyInseparable (M j) (L j) := fun j ↦ (hfields j).2.2.2.1
  let : ∀ j, Module.Finite (M j) (L j) := fun j ↦ inferInstance
  let : Algebra K (∀ j, M j) := (RingHom.pi (fun j ↦
    (algebraMap (GenericField (v j)) (M j)).comp (Pi.evalRingHom GenericField (v j)))).toAlgebra
  have hM := finite_etale_pi_of_componentwise GenericField v M
  let : Module.Finite K (∀ j, M j) := hM.1
  let : Algebra.Etale K (∀ j, M j) := hM.2
  let F : (∀ j, M j) →ₐ[K] (∀ j, L j) :=
    { __ := RingHom.pi (fun j ↦ (algebraMap (M j) (L j)).comp (Pi.evalRingHom M j))
      commutes' := fun r ↦ by
        funext j
        change algebraMap (M j) (L j)
          (algebraMap (GenericField (v j)) (M j) (r (v j))) =
            algebraMap (GenericField (v j)) (L j) (r (v j))
        exact (IsScalarTower.algebraMap_apply (GenericField (v j)) (M j) (L j) _).symm }
  have hFinj : Function.Injective F := by
    intro x y h
    funext j
    exact (algebraMap (M j) (L j)).injective (congrFun h j)
  have hFU : IsUniversalHomeomorphism F.toRingHom :=
    isUniversalHomeomorphism_pi_of_isPurelyInseparable M L
  have hFp : Function.Bijective (invertPrimeMap p F.toRingHom) := by
    apply invertPrimeMap_pi_bijective M L p
    intro j
    apply invertPrimeMap_bijective_of_field p (algebraMap (M j) (L j))
    intro hp
    apply (hfields j).2.2.2.2
    apply isUnit_iff_ne_zero.mpr
    intro hz
    apply hp.ne_zero
    simpa only [map_natCast, map_zero] using congrArg (algebraMap (GenericField (v j)) (M j)) hz
  let t : (∀ j, M j) →ₐ[K] B := e.symm.toAlgHom.comp F
  have htinj : Function.Injective t := e.symm.injective.comp hFinj
  have heU : IsUniversalHomeomorphism e.symm.toRingHom := by
    apply isUniversalHomeomorphism_of_nil_kernel _ e.symm.surjective
    rw [(RingHom.injective_iff_ker_eq_bot e.symm.toRingHom).mp e.symm.injective]
    exact bot_le
  have htU : IsUniversalHomeomorphism t.toRingHom :=
    isUniversalHomeomorphism_comp F.toRingHom e.symm.toRingHom hFU heU
  have htp : Function.Bijective (invertPrimeMap p t.toRingHom) := by
    change Function.Bijective (invertPrimeMap p (e.symm.toRingHom.comp F.toRingHom))
    rw [invertPrimeMap_comp]
    exact (invertPrimeMap_bijective p e.symm.toRingHom e.symm.bijective).comp hFp
  let C := t.range
  let eC := AlgEquiv.ofInjective t htinj
  refine ⟨C, Module.Finite.equiv eC.toLinearEquiv, Algebra.Etale.of_equiv eC, ?_, ?_⟩
  · exact isUniversalHomeomorphism_tower_top eC.toRingHom C.val.toRingHom htU
      Subtype.val_injective
  · apply (Function.Bijective.of_comp_iff (invertPrimeMap p C.val.toRingHom)
      (invertPrimeMap_bijective p eC.toRingHom eC.bijective)).mp
    change Function.Bijective ((invertPrimeMap p C.val.toRingHom).comp (invertPrimeMap p eC.toRingHom))
    rw [← invertPrimeMap_comp]
    exact htp

end SerrePositivity.CommutativeAlgebra
