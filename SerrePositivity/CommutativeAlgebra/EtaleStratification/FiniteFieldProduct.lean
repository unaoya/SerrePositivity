module

public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# 体の有限積上の有限代数

## 概要
有限代数の被約化を有限体拡大の積に分解し、各因子の基底の体を明示する。

## 方針
Artinian 環の極大イデアルによる分解を使い、体への射の核から基底の一成分を選ぶ。

## 規約
最後の積の代数構造も、選んだ基底成分への評価射を使って指定する。

## 使われ方
層別の一般点で有限エタール部分と純非分離部分を取り出す前段。
-/

@[expose] public section
noncomputable section
universe u

namespace SerrePositivity.CommutativeAlgebra

/-- 体の有限積から体への射は、ただ一つの成分への評価を経由する。 -/
private theorem exists_field_factor {ι : Type*} [Finite ι]
    (K : ι → Type*) [∀ i, Field (K i)] (L : Type*) [Field L]
    (f : (∀ i, K i) →+* L) :
    ∃ (i : ι) (g : K i →+* L), g.comp (Pi.evalRingHom K i) = f := by
  classical
  obtain ⟨i, q, hq⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq
    (⟨RingHom.ker f, RingHom.ker_isPrime f⟩ : PrimeSpectrum (∀ i, K i))
  obtain rfl : q = ⊥ := Subsingleton.elim _ _
  have hk : RingHom.ker (Pi.evalRingHom K i) ≤ RingHom.ker f :=
    (congrArg PrimeSpectrum.asIdeal hq).le
  let e := Pi.evalRingHom K i
  let g := e.liftOfRightInverse (Pi.single i) (by intro x; simp [e]) ⟨f, hk⟩
  exact ⟨i, g, e.liftOfRightInverse_comp (Pi.single i) (by intro x; simp [e]) ⟨f, hk⟩⟩

/-- 基底の一成分へ構造射を因子化すると、有限加群性がその体上へ移る。 -/
private theorem finite_field_factor {ι : Type*} (K : ι → Type*) [∀ i, Field (K i)]
    (L : Type*) [Field L] [Algebra (∀ i, K i) L] [Module.Finite (∀ i, K i) L]
    (i : ι) (g : K i →+* L) (hg : g.comp (Pi.evalRingHom K i) = algebraMap (∀ i, K i) L) :
    letI : Algebra (K i) L := g.toAlgebra
    Module.Finite (K i) L := by
  let : Algebra (K i) L := g.toAlgebra
  let : Algebra (∀ i, K i) (K i) := (Pi.evalRingHom K i).toAlgebra
  let : IsScalarTower (∀ i, K i) (K i) L :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (congrArg (fun h : (∀ i, K i) →+* L ↦ h x) hg).symm
  exact Module.Finite.of_restrictScalars_finite (∀ i, K i) (K i) L

/-- 体の有限積上の有限代数の被約化は、各基底成分上の有限体拡大の有限積。 -/
theorem finite_algebra_over_field_product {ι : Type u} [Finite ι]
    (K : ι → Type u) [∀ i, Field (K i)] (A : Type u) [CommRing A]
    [Algebra (∀ i, K i) A] [Module.Finite (∀ i, K i) A] :
    ∃ (m : ℕ) (v : Fin m → ι) (L : Fin m → Type u) (hL : ∀ j, Field (L j)),
      letI : ∀ j, Field (L j) := hL
      ∃ a : ∀ j, Algebra (K (v j)) (L j),
        letI : ∀ j, Algebra (K (v j)) (L j) := a
        letI : Algebra (∀ i, K i) (∀ j, L j) := (RingHom.pi (fun j ↦
          (algebraMap (K (v j)) (L j)).comp (Pi.evalRingHom K (v j)))).toAlgebra
        Nonempty ((A ⧸ nilradical A) ≃ₐ[∀ i, K i] (∀ j, L j)) ∧
          ∀ j, Module.Finite (K (v j)) (L j) := by
  classical
  let : IsArtinianRing A := isArtinian_of_tower (∀ i, K i) inferInstance
  let J := MaximalSpectrum A
  let F (j : J) := A ⧸ j.asIdeal
  let : ∀ j, Field (F j) := fun j ↦ Ideal.Quotient.field j.asIdeal
  choose v g hg using fun j : J ↦ exists_field_factor K (F j) (algebraMap (∀ i, K i) (F j))
  let : Fintype J := Fintype.ofFinite J
  let e := Fintype.equivFin J
  let L (j : Fin (Fintype.card J)) := F (e.symm j)
  let a (j : Fin (Fintype.card J)) : Algebra (K (v (e.symm j))) (L j) :=
    (g (e.symm j)).toAlgebra
  refine ⟨Fintype.card J, fun j ↦ v (e.symm j), L, inferInstance, a, ?_, ?_⟩
  · let E := (IsArtinianRing.quotNilradicalEquivPi A).toRingEquiv.trans
      (RingEquiv.piCongrLeft' F e)
    refine ⟨{ __ := E, commutes' := ?_ }⟩
    intro r
    funext j
    change algebraMap (∀ i, K i) (F (e.symm j)) r = g (e.symm j) (r (v (e.symm j)))
    exact (congrArg (fun h : (∀ i, K i) →+* F (e.symm j) ↦ h r) (hg (e.symm j))).symm
  · intro j
    exact finite_field_factor K (F (e.symm j)) (v (e.symm j)) (g (e.symm j)) (hg (e.symm j))

end SerrePositivity.CommutativeAlgebra
