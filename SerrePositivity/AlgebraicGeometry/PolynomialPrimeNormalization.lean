module

public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.RingTheory.TensorProduct.Finite

/-!
概要：多項式環の素イデアルを、有限自己写像で座標部分空間のイデアルに引き戻す。
方針：変数変換で素イデアルの元をモニックにし、一変数ずつ消去する。
規約：座標部分空間は、変数を零または残りの変数に送る全射で表す。
使われ方：相対 Noether 正規化で、指定した点の剰余体を制御する。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open Polynomial
open scoped Polynomial

private theorem finite_aeval_monic {A : Type*} [CommRing A] [Nontrivial A]
    (f : A[X]) (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    (Polynomial.aeval f : A[X] →ₐ[A] A[X]).Finite := by
  let g : A[X] →ₐ[A] A[X] := Polynomial.aeval f
  let relation : A[X][X] := f.map C - C X
  have hmap : (f.map C).Monic := hf.map C
  have hm : relation.Monic := by
    change (f.map C - C X).leadingCoeff = 1
    rw [leadingCoeff_sub_of_degree_lt, hmap.leadingCoeff]
    refine degree_C_le.trans_lt ?_
    rw [degree_eq_natDegree hmap.ne_zero, natDegree_map_eq_of_injective C_injective]
    exact WithBot.coe_lt_coe.mpr hdeg
  have hgC (a : A) : g (C a) = C a := by simp [g]
  have hr : relation.eval₂ g.toRingHom X = 0 := by
    have hcomp : g.toRingHom.comp C = C := RingHom.ext hgC
    change (f.map C - C X).eval₂ g.toRingHom X = 0
    rw [eval₂_sub, eval₂_map, hcomp, eval₂_C_X, eval₂_C]
    simp [g]
  let l := AdjoinRoot.lift g.toRingHom X hr
  have hl : Function.Surjective l := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
        obtain ⟨a, ha⟩ := hp
        obtain ⟨b, hb⟩ := hq
        exact ⟨a + b, by rw [map_add, ha, hb]⟩
    | monomial n a =>
        refine ⟨AdjoinRoot.of relation (C a) * AdjoinRoot.root relation ^ n, ?_⟩
        rw [map_mul, map_pow, AdjoinRoot.lift_of, AdjoinRoot.lift_root]
        change g (C a) * X ^ n = monomial n a
        rw [hgC, C_mul_X_pow_eq_monomial]
  have hfinite : (AdjoinRoot.of relation).Finite :=
    RingHom.finite_algebraMap.mpr hm.finite_adjoinRoot
  change g.toRingHom.Finite
  rw [← AdjoinRoot.lift_comp_of hr]
  exact (RingHom.Finite.of_surjective l hl).comp hfinite

private theorem finite_mapAlgHom {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (f : A →ₐ[k] B) (hf : f.Finite) :
    (Polynomial.mapAlgHom f).Finite := by
  let : Algebra A B := f.toRingHom.toAlgebra
  let : Algebra A[X] B[X] := Polynomial.algebra A B
  let : Module.Finite A B := hf
  change (algebraMap A[X] B[X]).Finite
  rw [RingHom.finite_algebraMap]
  exact Module.Finite.equiv (Algebra.IsPushout.equiv A A[X] B B[X]).toLinearEquiv

private theorem mem_ideal_iff_constantCoeff {A : Type*} [CommRing A]
    (I : Ideal A[X]) (hX : X ∈ I) (p : A[X]) :
    p ∈ I ↔ p.constantCoeff ∈ I.comap C := by
  have hsub : p - C p.constantCoeff ∈ I := by
    obtain ⟨q, hq⟩ := X_dvd_iff.mpr (show (p - C p.constantCoeff).coeff 0 = 0 by simp)
    rw [hq]
    exact I.mul_mem_right q hX
  change p ∈ I ↔ C p.constantCoeff ∈ I
  constructor
  · intro hp
    simpa using I.sub_mem hp hsub
  · intro hp
    simpa using I.add_mem hsub hp

set_option maxHeartbeats 800000 in
-- The recursive case checks finiteness through several changes of the coefficient algebra.
/--
概要：体上の多項式環の指定した素イデアルを、有限自己写像で座標イデアルに引き戻せる。
方針：Noether 正規化の変数変換の後、素イデアルのモニック元を一変数の像に選び、
残った変数について帰納する。
規約：引き戻したイデアルを、各変数を零または互いに異なる変数に送る全射の核で表す。
使われ方：相対 Noether 正規化で、指定した点の像の剰余体を純超越にする。
参考：Stacks Project, Tag 051P。
-/
theorem exists_finite_endomorphism_comap_eq_coordinate_ker
    {k : Type*} [Field k] {n : ℕ} (q : Ideal (MvPolynomial (Fin n) k)) [q.IsPrime] :
    ∃ (r : ℕ) (φ : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n) k)
      (δ : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin r) k),
      φ.Finite ∧ Function.Surjective δ ∧ q.comap φ.toRingHom = RingHom.ker δ.toRingHom ∧
        (∀ i, δ (MvPolynomial.X i) = 0 ∨ ∃ j, δ (MvPolynomial.X i) = MvPolynomial.X j) ∧
        Set.InjOn (fun i => δ (MvPolynomial.X i)) {i | δ (MvPolynomial.X i) ≠ 0} := by
  induction n with
  | zero =>
      have hq : q = ⊥ := by
        apply le_antisymm ?_ bot_le
        intro p hp
        rw [Ideal.mem_bot]
        by_contra hne
        have hc : MvPolynomial.constantCoeff p ≠ 0 := by
          intro h
          apply hne
          change p.coeff 0 = 0 at h
          rw [p.eq_C_of_isEmpty, h, map_zero]
        have hu : IsUnit p := p.eq_C_of_isEmpty ▸ (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C
        exact Ideal.IsPrime.ne_top ‹q.IsPrime› (q.eq_top_of_isUnit_mem hp hu)
      exact ⟨0, AlgHom.id k _, AlgHom.id k _, (RingHom.Finite.id _), Function.surjective_id,
        by
          change q.comap (RingHom.id _) = RingHom.ker (RingHom.id _)
          rw [Ideal.comap_id, hq, RingHom.ker_eq_comap_bot, Ideal.comap_id],
        fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ n ih =>
      by_cases hq : q = ⊥
      · refine ⟨n + 1, AlgHom.id k _, AlgHom.id k _, RingHom.Finite.id _,
          Function.surjective_id, ?_, fun i => Or.inr ⟨i, rfl⟩, ?_⟩
        · change q.comap (RingHom.id _) = RingHom.ker (RingHom.id _)
          rw [Ideal.comap_id, hq, RingHom.ker_eq_comap_bot, Ideal.comap_id]
        · exact MvPolynomial.X_injective.injOn
      obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hq
      let P := MvPolynomial (Fin n) k
      let split := MvPolynomial.finSuccEquiv k n
      let e := (NoetherNormalization.varChange f).trans split
      let I := q.comap e.symm.toRingHom
      let : I.IsPrime := Ideal.comap_isPrime _ _
      have hu : IsUnit (e f).leadingCoeff :=
        NoetherNormalization.varChange_leadingCoeff_isUnit f hf0
      let F : P[X] := hu.unit⁻¹ • e f
      have hF : F.Monic := monic_of_isUnit_leadingCoeff_inv_smul hu
      have hFI : F ∈ I := by
        apply I.smul_of_tower_mem
        change e.symm (e f) ∈ q
        simpa using hf
      have hdeg : 0 < F.natDegree := by
        by_contra! h
        have hd := Nat.eq_zero_of_le_zero h
        have he : F = C (F.coeff 0) := eq_C_of_natDegree_eq_zero hd
        have hc : F.coeff 0 = 1 := hd ▸ hF.leadingCoeff
        rw [he, hc, map_one] at hFI
        exact Ideal.IsPrime.ne_top ‹I.IsPrime› (I.eq_top_of_isUnit_mem hFI isUnit_one)
      let g : P[X] →ₐ[k] P[X] := (Polynomial.aeval F).restrictScalars k
      let J := I.comap g.toRingHom
      have hX : X ∈ J := by
        change Polynomial.aeval F X ∈ I
        simpa only [aeval_X] using hFI
      let J₀ := J.comap C
      let : J.IsPrime := Ideal.comap_isPrime _ _
      let : J₀.IsPrime := Ideal.comap_isPrime _ _
      obtain ⟨r, φ, δ, hφ, hδ, hker, hvars, hdistinct⟩ := ih J₀
      let ψ := e.symm.toAlgHom.comp
        (g.comp ((Polynomial.mapAlgHom φ).comp split.toAlgHom))
      let ε : P[X] →ₐ[k] P := { Polynomial.constantCoeff with
        commutes' := fun a => by simp }
      refine ⟨r, ψ, δ.comp (ε.comp split.toAlgHom), ?_,
        hδ.comp (constantCoeff_surjective.comp split.surjective), ?_, ?_⟩
      · have hg : g.Finite := finite_aeval_monic F hF hdeg
        have he : e.symm.toAlgHom.Finite :=
          AlgHom.Finite.of_surjective _ e.symm.surjective
        have hs : split.toAlgHom.Finite := AlgHom.Finite.of_surjective _ split.surjective
        exact he.comp (hg.comp ((finite_mapAlgHom φ hφ).comp hs))
      · ext p
        change Polynomial.mapAlgHom φ (split p) ∈ J ↔ δ ((split p).constantCoeff) = 0
        rw [mem_ideal_iff_constantCoeff J hX]
        change ((split p).map φ.toRingHom).coeff 0 ∈ J₀ ↔ _
        rw [Polynomial.coeff_map]
        change (split p).constantCoeff ∈ J₀.comap φ.toRingHom ↔ _
        rw [hker]
        rfl
      · let v := fun i => (δ.comp (ε.comp split.toAlgHom)) (MvPolynomial.X i)
        have hv₀ : v 0 = 0 := by
          change δ ((split (MvPolynomial.X 0)).constantCoeff) = 0
          simp [split, MvPolynomial.finSuccEquiv_X_zero]
        have hvₛ (j : Fin n) : v j.succ = δ (MvPolynomial.X j) := by
          change δ ((split (MvPolynomial.X j.succ)).constantCoeff) = δ (MvPolynomial.X j)
          simp [split, MvPolynomial.finSuccEquiv_X_succ]
        constructor
        · change ∀ i, v i = 0 ∨ ∃ j, v i = MvPolynomial.X j
          intro i
          refine Fin.cases (Or.inl hv₀) (fun j => ?_) i
          rw [hvₛ]
          exact hvars j
        · change Set.InjOn v {i | v i ≠ 0}
          intro i hi j hj hij
          change v i ≠ 0 at hi
          change v j ≠ 0 at hj
          change v i = v j at hij
          rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
          · exact (hi hv₀).elim
          rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
          · exact (hj hv₀).elim
          apply congrArg Fin.succ
          exact hdistinct
            (by simpa only [Set.mem_ofPred_eq, hvₛ] using hi)
            (by simpa only [Set.mem_ofPred_eq, hvₛ] using hj)
            (by simpa only [hvₛ] using hij)

end SerrePositivity.AlgebraicGeometry
