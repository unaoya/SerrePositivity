module
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Composition


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Prismatic.Envelopes.CompletedFreeDeltaResidue
public import SerrePositivity.BhattScholze.Prismatic.Envelopes.VariableEnvelope
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletelyFlatPrincipalCompletion
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.RegularReduction
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# 完備自由 δ 環の完備平坦性

## 概要
有界な向き付き prism 上の完備自由 δ 環は基底の二元イデアルに関して完全平坦。

## 方針
基底生成元が両辺で正則なので、その剰余の p 完全平坦性を示す。
剰余は多項式環の p 完備化であり、平坦な多項式拡大と主元完備化の完全平坦性を合成する。

## 使われ方
変数に沿う prismatic envelope の存在。
-/

public section

universe u

open CategoryTheory SerrePositivity.DerivedCompletion

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false

attribute [local instance] principalAdicQuotientAlgebra

private theorem polynomial_completion_flat {k σ : Type u} [CommRing k] (p : ℕ)
    (hk : ∃ N : ℕ, ∀ (n : ℕ) (x : k), (p : k)^n * x = 0 → (p : k)^N * x = 0) :
    let B := MvPolynomial σ k
    let D := PrincipalCompletionH0 B (p : B)
    let : CommRing D := principalCompletionCommRing B (p : B)
    let := ((principalCompletionUnitRingHom B (p : B)).comp MvPolynomial.C).toAlgebra
    IsCompletelyFlat (Ideal.span {(p : k)}) D := by
  let B := MvPolynomial σ k
  let D := PrincipalCompletionH0 B (p : B)
  let : CommRing D := principalCompletionCommRing B (p : B)
  let f : k →+* B := MvPolynomial.C
  let g : B →+* D := principalCompletionUnitRingHom B (p : B)
  have hpoly : IsCompletelyFlat (Ideal.span {(p : k)}) B := by
    let : Module.Flat k B := inferInstance
    intro M _ _ _
    apply (isConcentratedInDegreeZero_derivedTensor_iff B M).mpr
    intro i hi
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
    exact torModule_subsingleton_of_flat B M j
  obtain ⟨N, hN⟩ := hk
  have hB : ∃ N : ℕ, ∀ (n : ℕ) (x : B), (p : B)^n • x = 0 → (p : B)^N • x = 0 := by
    refine ⟨N, fun n x hx => ?_⟩
    change (p : B)^n * x = 0 at hx
    change (p : B)^N * x = 0
    apply MvPolynomial.ext
    intro m
    have hc (j : ℕ) :
        (((p : B) ^ j) * x).coeff m = (p : k) ^ j * x.coeff m := by
      rw [← map_natCast MvPolynomial.C, ← map_pow, MvPolynomial.coeff_C_mul]
    rw [hc, AddMonoidAlgebra.coeff_zero]
    apply hN n
    have hm := congrArg (fun y : B => y.coeff m) hx
    rwa [hc, AddMonoidAlgebra.coeff_zero] at hm
  have hg : g.toAlgebra = principalCompletionAlgebra B (p : B) :=
    Algebra.algebra_ext _ _ fun _ => rfl
  have hcomp : @IsCompletelyFlat B _ ((Ideal.span {(p : k)}).map f) D _
      g.toAlgebra.toModule := by
    rw [hg, Ideal.map_span, Set.image_singleton, map_natCast]
    exact (Andre.Transfinite.principalCompletionH0_isCompletelyFaithfullyFlat B (p : B) hB).1
  have hf : f.toAlgebra = (inferInstance : Algebra k B) :=
    Algebra.algebra_ext _ _ fun _ => rfl
  have hpoly' : @IsCompletelyFlat k _ (Ideal.span {(p : k)}) B _
      f.toAlgebra.toModule := by
    rw [hf]
    exact hpoly
  exact Andre.Transfinite.isCompletelyFlat_comp f g _ hpoly' hcomp

/-- 有界 prism 上の完備自由 δ 環は (p,d) 完全平坦。 -/
theorem completedFreeDelta_completelyFlat {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
    (P : OrientedPrism p A) (hP : IsBoundedPrism P) (S : Type u) :
    let := (completedFreeDeltaBase P S).toAlgebra
    IsCompletelyFlat (Ideal.span {(p : A), P.generator}) (completedFreeDelta P S) := by
  let C := completedFreeDelta P S
  let b : A →+* C := completedFreeDeltaBase P S
  let : Algebra A C := b.toAlgebra
  let E := C ⧸ Ideal.span {b P.generator}
  let k := A ⧸ P.ideal
  let : Algebra k E := principalAdicQuotientAlgebra P.generator C
  let B := MvPolynomial (S × ℕ) k
  let D := PrincipalCompletionH0 B (p : B)
  let : CommRing D := principalCompletionCommRing B (p : B)
  let j : B →+* D := principalCompletionUnitRingHom B (p : B)
  let : Algebra k D := (j.comp MvPolynomial.C).toAlgebra
  let e : E ≃+* D := completedFreeDeltaResidueEquiv P S
  have he : IsSMulRegular C (algebraMap A C P.generator) := by
    intro x y h
    apply completedFreeDelta_generator_regular P hP S
    change (algebraMap A C P.generator) • x = (algebraMap A C P.generator) • y at h
    rw [Algebra.smul_def, Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply] at h
    exact h
  apply Andre.completelyFlat_pair_algebra_of_regular_reduction (p : A) P.generator
    (show IsSMulRegular A P.generator from P.generator_regular) C he
  change IsCompletelyFlat (Ideal.span {Ideal.Quotient.mk P.ideal (p : A)}) E
  rw [map_natCast]
  let e' : E ≃ₐ[k] D := {
    e with
    commutes' := by
      intro a
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
      change e (Ideal.Quotient.mk _ (b x)) = j (MvPolynomial.C (Ideal.Quotient.mk P.ideal x))
      exact (completedFreeDeltaResidueEquiv_unit P S (MvPolynomial.C x)).trans
        (congrArg j (MvPolynomial.map_C _ _))
  }
  exact isCompletelyFlat_of_linearEquiv _ e'.symm.toLinearEquiv (polynomial_completion_flat p hP)

/-- 概要：完備自由 δ 環の指定変数に沿う有界な envelope は存在し、基底上で完全平坦
（BS 著者版 Example 3.14）。
方針：指定変数を基底生成元倍へ送る置換を、正則な完備自由 δ 環に取る。
規約：envelope のイデアルは基底生成元の像で生成される。
使われ方：affine Čech–Alexander 模型の各次数。 -/
theorem exists_prismaticEnvelope_of_variables {p : ℕ} [Fact p.Prime]
    {A : Type u} [CommRing A] (P : OrientedPrism p A) (hP : IsBoundedPrism P)
    (S : Type u) (Z : Set S) :
    ∃ (C : Type u) (rc : CommRing C),
      letI := rc
      ∃ (Q : OrientedPrism p C) (η : completedFreeDelta P S →+* C),
      IsPrismaticEnvelope P (completedFreeDeltaStructure P S) (completedFreeDeltaBase P S)
        (completedFreeDeltaBase_isDeltaHom P S) (variableIdeal P S Z)
        (Ideal.subset_span (Set.mem_insert _ _)) Q η ∧
      IsBoundedPrism Q ∧
      (letI : Algebra A C := (η.comp (completedFreeDeltaBase P S)).toAlgebra;
        IsCompletelyFlat (Ideal.span {(p : A), P.generator}) C) := by
  let C := completedFreeDelta P S
  let hreg := completedFreeDelta_generator_regular P hP S
  let Q := completedFreeDeltaPrism P S hreg
  let η := variableEnvelopeSubstitution P S Z
  have hQ : IsBoundedPrism Q := by
    unfold IsBoundedPrism
    rw [completedFreeDeltaPrism_ideal]
    exact completedFreeDelta_residue_bounded P hP S
  refine ⟨C, inferInstance, Q, η, isPrismaticEnvelope_variableSubstitution P S Z hreg, hQ, ?_⟩
  change @IsCompletelyFlat A _ (Ideal.span {(p : A), P.generator}) C _
    (η.comp (completedFreeDeltaBase P S)).toAlgebra.toModule
  rw [variableEnvelopeSubstitution_base]
  exact completedFreeDelta_completelyFlat P hP S

end SerrePositivity.BhattScholze.Prismatic

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Ex 3.14" (partial := special) "自由変数（候補環の生成元が正則）の envelope。一般の滑らかな B₀ → R は未 ／ 11-10 更新"] _root_.SerrePositivity.BhattScholze.Prismatic.exists_prismaticEnvelope_of_variables
attribute [cite BS19 "Prop 3.13" (partial := special) "向き付き・B＝完備自由 δ 環・J＝(d, 変数) の場合に存在と完全平坦性 (1)。底変換 (2) は変数の場合が本体（prismaticEnvelope_completedBaseChange_of_variables）。一般の正則な B, J は未 ／ 11-10 更新 ／ 11-12 夜更新（ノート本文の更新時）"] _root_.SerrePositivity.BhattScholze.Prismatic.exists_prismaticEnvelope_of_variables
