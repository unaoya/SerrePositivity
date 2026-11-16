module

public import SerrePositivity.BhattScholze.Semiperfectoid.Lci.LciEnvelopeResidue
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PDCompletionResidue
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Composition
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletelyFlatPrincipalCompletion

/-!
# 普遍除算の完備生成元剰余

## 概要
普遍除算の生成元剰余の完全平坦性を、自由変数環の二座標完備化後に移す。

## 方針
完備化の生成元剰余を元の剰余の p 完備化に同定し、完全平坦な射を合成する。

## 規約
BS 著者版 Example 7.9 の普遍変数模型。

## 使われ方
有界 p 冪ねじれを持つ正則列の商への底変換。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

namespace SerrePositivity.BhattScholze

open _root_.SerrePositivity.DerivedCompletion

variable {p : ℕ} [Fact p.Prime] {A S : Type u} [CommRing A]

/-- 概要：完備した普遍自由変数包絡の d 剰余は、初期関係の商上 p 完全平坦。
方針：未完備の d 剰余の完全平坦性に主元完備化の完全平坦性を合成し、標準剰余同型で移す。
規約：BS 著者版 Example 7.9。係数と係数の d 商の p 正則性を使う。
使われ方：一般の正則列に対する完備底変換の離散性。 -/
theorem Semiperfectoid.exists_completedFreeVariable_generatorResidue_completelyFlat
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (d : A)
    (hp : Function.Injective (fun x : A => (p : A) * x))
    (hpd : Function.Injective (fun x : A ⧸ Ideal.span {d} => (p : A ⧸ Ideal.span {d}) * x))
    (u : Aˣ) (hu : (u : A) = D.delta d) :
    let U := _root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) S
    let K : Ideal U := Ideal.span {MvPolynomial.C d}
    let J : Ideal U := K ⊔ Ideal.span (Set.range fun s : S => MvPolynomial.X (s, 0))
    let H := PDCompletionH0 U p (MvPolynomial.C d)
    let := pdCompletionCommRing U p (MvPolynomial.C d)
    let j := pdCompletionUnit U p (MvPolynomial.C d)
    let L : Ideal H := Ideal.span {j (MvPolynomial.C d)}
    ∃ b : U ⧸ J →+* H ⧸ L,
      (∀ z : U, b (Ideal.Quotient.mk J z) =
        Ideal.Quotient.mk L (j (_root_.SerrePositivity.BhattScholze.deltaDivisionSourceMap D d z))) ∧
      let := b.toAlgebra
      _root_.SerrePositivity.IsCompletelyFlat (Ideal.span {(p : U ⧸ J)}) (H ⧸ L) := by
  let U := _root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) S
  let C : A →+* U := MvPolynomial.C
  let K : Ideal U := Ideal.span {C d}
  let J : Ideal U := K ⊔ Ideal.span (Set.range fun s : S => MvPolynomial.X (s, 0))
  let T := U ⧸ J
  let V := U ⧸ K
  let W := PrincipalCompletionH0 V (p : V)
  let := principalCompletionCommRing V (p : V)
  let H := PDCompletionH0 U p (C d)
  let := pdCompletionCommRing U p (C d)
  let j := pdCompletionUnit U p (C d)
  let L : Ideal H := Ideal.span {j (C d)}
  let e : (H ⧸ L) ≃+* W := pdCompletionResidueEquiv U p (C d)
  let j₀ : V →+* W := principalCompletionUnitRingHom V (p : V)
  have hK : K = (Ideal.span {d}).map C := by
    rw [Ideal.map_span, Set.image_singleton]
  let eK := (Ideal.quotEquivOfEq hK).trans
    (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := S × ℕ) (Ideal.span {d})).symm.toRingEquiv
  have hV : IsSMulRegular V (p : V) := by
    have hpoly : IsSMulRegular (MvPolynomial (S × ℕ) (A ⧸ Ideal.span {d}))
        (p : MvPolynomial (S × ℕ) (A ⧸ Ideal.span {d})) := by
      simpa only [map_natCast, IsSMulRegular, smul_eq_mul] using
        (show IsSMulRegular (A ⧸ Ideal.span {d}) (p : A ⧸ Ideal.span {d}) from hpd).of_flat
          (S := MvPolynomial (S × ℕ) (A ⧸ Ideal.span {d}))
    intro x y hxy
    apply eK.injective
    apply hpoly
    simpa only [map_mul, map_natCast, smul_eq_mul] using congrArg eK hxy
  have hbound : ∃ N : ℕ, ∀ (n : ℕ) (x : V),
      (p : V) ^ n • x = 0 → (p : V) ^ N • x = 0 := by
    refine ⟨0, fun n x hx => ?_⟩
    have hx₀ : x = 0 := (hV.pow n) (by simpa only [smul_zero] using hx)
    rw [hx₀, smul_zero]
  obtain ⟨b₀, hb₀, hflat₀⟩ :=
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.exists_freeVariable_generatorResidue_completelyFlat (S := S) D d hp hpd u hu
  let b : T →+* H ⧸ L := e.symm.toRingHom.comp (j₀.comp b₀)
  refine ⟨b, ?_, ?_⟩
  · intro z
    apply e.injective
    change e (e.symm (j₀ (b₀ (Ideal.Quotient.mk J z)))) =
      e (Ideal.Quotient.mk L (j (_root_.SerrePositivity.BhattScholze.deltaDivisionSourceMap D d z)))
    rw [e.apply_symm_apply, pdCompletionResidueEquiv_unit, hb₀]
  · letI := b₀.toAlgebra
    let := (j₀.comp b₀).toAlgebra
    let := b.toAlgebra
    have hcomp : _root_.SerrePositivity.IsCompletelyFlat (Ideal.span {(p : T)}) W := by
      have hW : @_root_.SerrePositivity.IsCompletelyFlat V _ ((Ideal.span {(p : T)}).map b₀) W _
          j₀.toAlgebra.toModule := by
        have hAlgebra : j₀.toAlgebra = principalCompletionAlgebra V (p : V) :=
          Algebra.algebra_ext _ _ fun _ => rfl
        rw [hAlgebra, Ideal.map_span, Set.image_singleton, map_natCast]
        exact (_root_.SerrePositivity.BhattScholze.Andre.Transfinite.principalCompletionH0_isCompletelyFaithfullyFlat
          V (p : V) hbound).1
      exact _root_.SerrePositivity.BhattScholze.Andre.Transfinite.isCompletelyFlat_comp b₀ j₀ _ hflat₀ hW
    let eA : (H ⧸ L) ≃ₐ[T] W := AlgEquiv.ofRingEquiv (f := e) fun _ =>
      e.apply_symm_apply _
    exact _root_.SerrePositivity.isCompletelyFlat_of_linearEquiv _ eA.symm.toLinearEquiv hcomp

end SerrePositivity.BhattScholze
