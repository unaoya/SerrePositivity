module

public import SerrePositivity.BhattScholze.Prism.Perfectoid.WittQuotientFrobeniusKernel
public import SerrePositivity.CommutativeAlgebra.PerfectionPrincipalKernel

/-! # Witt商への係数射とtilt持上げ

S=W(k)/(d)のmod p係数射を、既存Perfection.liftでtiltへ持ち上げる。
untiltの式にはSの古典的p進完備性とpの非可逆性を明示的に仮定する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (k : Type u) [CommRing k] [CharP k p] [PerfectRing k p]

/-- kからWitt商mod pへの標準係数環射。既存の商同型を逆に使う。 -/
def wittQuotientCoefficientMap (d : WittVector p k) :
    k →+* ModP (WittVector p k ⧸ Ideal.span {d}) p :=
  (wittQuotientModPEquiv p k d).symm.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {d.coeff 0}))

/-- 標準係数射はTeichmüller元を二度商へ送る式に一致する。 -/
@[simp] theorem wittQuotientCoefficientMap_apply (d : WittVector p k) (x : k) :
    wittQuotientCoefficientMap p k d x =
      Ideal.Quotient.mk (Ideal.span {(p : WittVector p k ⧸ Ideal.span {d})})
        (Ideal.Quotient.mk (Ideal.span {d}) (WittVector.teichmuller p x)) := by
  apply (wittQuotientModPEquiv p k d).injective
  simp [wittQuotientCoefficientMap]

/-- 標準係数射は全射。 -/
theorem wittQuotientCoefficientMap_surjective (d : WittVector p k) :
    Function.Surjective (wittQuotientCoefficientMap p k d) :=
  (wittQuotientModPEquiv p k d).symm.surjective.comp Ideal.Quotient.mk_surjective

variable (d : WittVector p k) [Fact (¬ IsUnit (p : WittVector p k ⧸ Ideal.span {d}))]

/-- 標準係数射のtiltへの一意な持上げ。一般Perfectionの既存APIを使う。 -/
def wittQuotientTiltMap : k →+* PreTilt (WittVector p k ⧸ Ideal.span {d}) p :=
  Perfection.lift p k _ (wittQuotientCoefficientMap p k d)

/-- tilt持上げの全座標は、逆Frobenius反復の標準係数像。 -/
theorem wittQuotientTiltMap_coeff (n : ℕ) (x : k) :
    PreTilt.coeff n (wittQuotientTiltMap p k d x) =
      wittQuotientCoefficientMap p k d (((_root_.frobeniusEquiv k p).symm : k → k)^[n] x) := rfl

/-- tilt持上げのuntiltは、Witt商のTeichmüller元の標準像。 -/
theorem wittQuotientTiltMap_untilt
    [IsAdicComplete (Ideal.span {(p : WittVector p k ⧸ Ideal.span {d})})
      (WittVector p k ⧸ Ideal.span {d})] (x : k) :
    (wittQuotientTiltMap p k d x).untilt =
      Ideal.Quotient.mk (Ideal.span {d}) (WittVector.teichmuller p x) := by
  apply Perfection.teichmullerFun_spec
  intro n
  let a := ((_root_.frobeniusEquiv k p).symm : k → k)^[n] x
  refine ⟨Ideal.Quotient.mk (Ideal.span {d}) (WittVector.teichmuller p a), ?_, ?_⟩
  · change Ideal.Quotient.mk (Ideal.span {(p : WittVector p k ⧸ Ideal.span {d})})
      (Ideal.Quotient.mk (Ideal.span {d}) (WittVector.teichmuller p a)) =
        PreTilt.coeff n (wittQuotientTiltMap p k d x)
    rw [wittQuotientTiltMap_coeff, wittQuotientCoefficientMap_apply]
  · have ha : a ^ (p ^ n) = x := iterate_frobeniusEquiv_symm_pow_p_pow k p x n
    rw [← map_pow, ← map_pow, ha]
    exact SModEq.refl _

/-- d₀のtilt像の第0座標は零。Fontaine核の候補の第0成分に使う。 -/
theorem wittQuotientTiltMap_coeff_zero_d :
    PreTilt.coeff 0 (wittQuotientTiltMap p k d (d.coeff 0)) = 0 := by
  rw [wittQuotientTiltMap_coeff]
  change (wittQuotientModPEquiv p k d).symm
    (Ideal.Quotient.mk (Ideal.span {d.coeff 0}) (d.coeff 0)) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp)), map_zero]

/-- tiltの第0射影の核の元は、各座標でd₀のtilt像によって割り切れる。
互換的な商の列を構成する工程とは分けた具体的な座標判定。 -/
theorem wittQuotientTilt_kernel_coeff_dvd
    (x : PreTilt (WittVector p k ⧸ Ideal.span {d}) p) (hx : PreTilt.coeff 0 x = 0) (n : ℕ) :
    PreTilt.coeff n (wittQuotientTiltMap p k d (d.coeff 0)) ∣ PreTilt.coeff n x := by
  let a := ((_root_.frobeniusEquiv k p).symm : k → k)^[n] (d.coeff 0)
  have ha : a ^ (p ^ n) = d.coeff 0 := iterate_frobeniusEquiv_symm_pow_p_pow k p _ n
  have hxn : (PreTilt.coeff n x) ^ (p ^ n) = 0 := by
    have h := compatibleRoots_pow p (fun m ↦ PreTilt.coeff m x)
      (fun m ↦ Perfection.coeff_pow_p' x m) 0 n
    simpa only [Nat.zero_add, hx] using h
  have hmem := (wittQuotientModP_pow_prime_pow_eq_zero_iff_mem_span p k d n a ha
    (PreTilt.coeff n x)).mp hxn
  apply Ideal.mem_span_singleton.mp
  rw [wittQuotientTiltMap_coeff, wittQuotientCoefficientMap_apply]
  exact hmem

end SerrePositivity.BhattScholze
