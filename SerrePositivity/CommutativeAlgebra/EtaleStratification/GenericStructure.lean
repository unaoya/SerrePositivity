module

public import SerrePositivity.CommutativeAlgebra.EtaleStratification.GenericPoints
public import SerrePositivity.CommutativeAlgebra.EtaleStratification.GenericSeparable
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.Algebra.CharP.IntermediateField

/-!
# 一般点での有限代数の分解

## 概要
被約 noetherian 基底の全商環上で、有限代数の被約化を体拡大の積に分解する。

## 方針
全商環の有限積表示と Artinian 代数の分解を組み合わせ、各体拡大の分離閉包を取る。

## 規約
p 可逆な成分は Z_(p) 代数の仮定から標数 0 になる。

## 使われ方
有限エタール層別の一般点での構造。
-/

@[expose] public section
noncomputable section
universe u

namespace SerrePositivity.CommutativeAlgebra

open scoped TensorProduct

/-- 有限分離体拡大はエタール。一般点での分離部分に用いる。 -/
theorem etale_of_finite_separable (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] : Algebra.Etale K L := by
  exact ⟨Algebra.FormallyEtale.of_isSeparable K L,
    Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

/-- Z_(p) 環から射を持つ体で p が可逆なら、全素数が非零なので標数 0。 -/
theorem strataField_charZero_of_isUnit {R K : Type u} [CommRing R] [Field K]
    (p : ℕ) (hZp : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R))
    (f : R →+* K) (hp : IsUnit (p : K)) : CharZero K := by
  apply (CharZero.charZero_iff_forall_prime_ne_zero K).mpr
  intro q hq
  by_cases he : q = p
  · subst q
    exact hp.ne_zero
  · have hu := (hZp q hq he).map f
    rw [map_natCast] at hu
    exact hu.ne_zero

/-- 一般点の剰余体について、p 可逆な因子は標数 0。 -/
theorem genericField_charZero_of_isUnit (R : Type u) [CommRing R]
    (p : ℕ) (hZp : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R))
    (P : GenericPoint R) (hp : IsUnit (p : GenericField P)) : CharZero (GenericField P) :=
  strataField_charZero_of_isUnit p hZp (algebraMap R (GenericField P)) hp

/-- 有限体拡大の分離部分は有限エタール、残りは純非分離。
p 可逆から標数 0 が従う場合には、後半の射は全単射になる。 -/
theorem separableClosure_strata_factorization (K L : Type u) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] (p : ℕ)
    (hchar : IsUnit (p : K) → CharZero K) :
    let M := separableClosure K L
    Module.Finite K M ∧ Algebra.Etale K M ∧ IsPurelyInseparable M L ∧
      (IsUnit (p : K) → Function.Bijective (algebraMap M L)) := by
  let M := separableClosure K L
  refine ⟨inferInstance, etale_of_finite_separable K M, inferInstance, ?_⟩
  intro hp
  let : CharZero K := hchar hp
  let : CharZero M := inferInstance
  exact IsPurelyInseparable.bijective_algebraMap_of_isSeparable M L

/-- 概要：noetherian 被約 R_0 の全商環 K = ∏ κ(𝔭_i)（極小素イデアル）上で、S_0 ⊗ K の被約化は有限体拡大の有限積 ∏ L_i、各 κ(𝔭_i) → L_i は
分離閉包 M_i を経て κ → M_i 有限エタール、M_i → L_i 純非分離。
方針：Mathlib `minimalPrimes`（有限）、有限被約 K 代数＝体の積、`separableClosure`。 -/
theorem generic_structure (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsReduced R] [Module.Finite R S] (p : ℕ) [Fact p.Prime]
    (hZp : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    letI : Algebra R (GenericProduct R) := (genericProductMap R).toAlgebra
    letI : Module R (GenericProduct R) := Algebra.toModule
    Finite (GenericPoint R) ∧ IsLocalization (nonZeroDivisors R) (GenericProduct R) ∧
      (∀ P : GenericPoint R, IsUnit (p : GenericField P) → CharZero (GenericField P)) ∧
      ∃ (m : ℕ) (v : Fin m → GenericPoint R) (L : Fin m → Type u) (hL : ∀ j, Field (L j)),
        letI : ∀ j, Field (L j) := hL
        ∃ a : ∀ j, Algebra (GenericField (v j)) (L j),
          letI : ∀ j, Algebra (GenericField (v j)) (L j) := a
          letI : Algebra (GenericProduct R) (∀ j, L j) := (RingHom.pi (fun j =>
            (algebraMap (GenericField (v j)) (L j)).comp
              (Pi.evalRingHom GenericField (v j)))).toAlgebra
          Nonempty (((GenericProduct R ⊗[R] S) ⧸ nilradical (GenericProduct R ⊗[R] S))
            ≃ₐ[GenericProduct R] (∀ j, L j)) ∧
            ∀ j,
              let k := GenericField (v j)
              let M := separableClosure k (L j)
              FiniteDimensional k (L j) ∧ Module.Finite k M ∧ Algebra.Etale k M ∧
                IsPurelyInseparable M (L j) ∧
                (IsUnit (p : k) → Function.Bijective (algebraMap M (L j))) := by
  let : Algebra R (GenericProduct R) := (genericProductMap R).toAlgebra
  let : Module R (GenericProduct R) := Algebra.toModule
  have hdecomp : IsLocalization (nonZeroDivisors R) (GenericProduct R) ∧
      ∃ (m : ℕ) (v : Fin m → GenericPoint R) (L : Fin m → Type u) (hL : ∀ j, Field (L j)),
        letI : ∀ j, Field (L j) := hL
        ∃ a : ∀ j, Algebra (GenericField (v j)) (L j),
          letI : ∀ j, Algebra (GenericField (v j)) (L j) := a
          letI : Algebra (GenericProduct R) (∀ j, L j) := (RingHom.pi (fun j =>
            (algebraMap (GenericField (v j)) (L j)).comp
              (Pi.evalRingHom GenericField (v j)))).toAlgebra
          Nonempty (((GenericProduct R ⊗[R] S) ⧸ nilradical (GenericProduct R ⊗[R] S))
            ≃ₐ[GenericProduct R] (∀ j, L j)) ∧
            ∀ j, FiniteDimensional (GenericField (v j)) (L j) := by
    let : Finite (GenericPoint R) := finite_genericPoint R
    exact ⟨isLocalization_genericProduct R,
      finite_algebra_over_field_product GenericField (GenericProduct R ⊗[R] S)⟩
  obtain ⟨hloc, m, v, L, hL, a, he, hfinite⟩ := hdecomp
  let : ∀ j, Field (L j) := hL
  let : ∀ j, Algebra (GenericField (v j)) (L j) := a
  refine ⟨finite_genericPoint R, hloc,
    fun P hp ↦ genericField_charZero_of_isUnit R p hZp P hp,
    m, v, L, hL, a, he, ?_⟩
  intro j
  let : FiniteDimensional (GenericField (v j)) (L j) := hfinite j
  exact ⟨hfinite j, separableClosure_strata_factorization
    (GenericField (v j)) (L j) p (genericField_charZero_of_isUnit R p hZp (v j))⟩

end SerrePositivity.CommutativeAlgebra
