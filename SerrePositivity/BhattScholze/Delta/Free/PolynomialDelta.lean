module

public import SerrePositivity.BhattScholze.Delta.DeltaSectionNaturality
public import Mathlib.Algebra.MvPolynomial.CommRing

/-! # 変数のδ値を指定した多項式δ構造

基底のW₂切断を係数に用い、変数を指定された二つのWitt座標へ送る。
また、任意の多項式δ構造からの環射がδ射であることを係数と変数上で判定する。
-/

@[expose] public noncomputable section
universe u v w
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] (σ : Type v)

/-- 係数のδ切断を延長し、各変数のδ値を指定するW₂切断。 -/
def polynomialDeltaSection (D : DeltaStructure p R) (v : σ → MvPolynomial σ R) :
    MvPolynomial σ R →+* WittTwo p (MvPolynomial σ R) :=
  MvPolynomial.eval₂Hom ((wittTwoMap (p := p) MvPolynomial.C).comp D.sectionHom)
    (fun s ↦ TruncatedWittVector.mk p (fun i ↦ if i = 0 then MvPolynomial.X s else v s))

/-- 多項式切断は係数上で元の切断をW₂係数写像で移したもの。 -/
@[simp] theorem polynomialDeltaSection_C (D : DeltaStructure p R)
    (v : σ → MvPolynomial σ R) (r : R) :
    polynomialDeltaSection σ D v (MvPolynomial.C r) =
      wittTwoMap MvPolynomial.C (D.sectionHom r) :=
  MvPolynomial.eval₂Hom_C _ _ r

/-- 多項式切断の変数上のW₂座標。有限段との自然性でもこの式を使う。 -/
@[simp] theorem polynomialDeltaSection_X (D : DeltaStructure p R)
    (v : σ → MvPolynomial σ R) (s : σ) :
    polynomialDeltaSection σ D v (MvPolynomial.X s) =
      TruncatedWittVector.mk p (fun i ↦ if i = 0 then MvPolynomial.X s else v s) :=
  MvPolynomial.eval₂Hom_X' _ _ s

/-- 指定した変数δ値によらず、W₂切断の第0座標は恒等射。 -/
theorem polynomialDeltaSection_projection (D : DeltaStructure p R)
    (v : σ → MvPolynomial σ R) :
    (wittTwoProjection p (MvPolynomial σ R)).comp (polynomialDeltaSection σ D v) =
      RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, polynomialDeltaSection, MvPolynomial.eval₂Hom_C,
      wittTwoProjection_apply, wittTwoMap_coeff]
    rw [D.coeff_zero]
    rfl
  · intro s
    simp [polynomialDeltaSection]

/-- 係数のδ構造と各変数のδ値から得られる多項式δ構造。 -/
def polynomialDeltaStructure (D : DeltaStructure p R) (v : σ → MvPolynomial σ R) :
    DeltaStructure p (MvPolynomial σ R) where
  sectionHom := polynomialDeltaSection σ D v
  coeff_zero := by
    intro f
    exact RingHom.congr_fun (polynomialDeltaSection_projection σ D v) f

/-- 多項式δ構造は係数上で元のδ構造に一致する。 -/
@[simp] theorem polynomialDeltaStructure_delta_C (D : DeltaStructure p R)
    (v : σ → MvPolynomial σ R) (r : R) :
    (polynomialDeltaStructure σ D v).delta (MvPolynomial.C r) =
      MvPolynomial.C (D.delta r) := by
  simp [DeltaStructure.delta, polynomialDeltaStructure, polynomialDeltaSection]

/-- 多項式δ構造は各変数上で指定したδ値を持つ。 -/
@[simp] theorem polynomialDeltaStructure_delta_X (D : DeltaStructure p R)
    (v : σ → MvPolynomial σ R) (s : σ) :
    (polynomialDeltaStructure σ D v).delta (MvPolynomial.X s) = v s := by
  simp [DeltaStructure.delta, polynomialDeltaStructure, polynomialDeltaSection]

/-- 多項式δ構造への係数射はδ射。 -/
theorem polynomialDeltaStructure_C_isDeltaHom (D : DeltaStructure p R)
    (v : σ → MvPolynomial σ R) :
    D.IsDeltaHom (polynomialDeltaStructure σ D v) MvPolynomial.C := by
  intro r
  exact (polynomialDeltaStructure_delta_C σ D v r).symm

namespace DeltaStructure
variable {σ} {A : Type w} [CommRing A]

/-- 係数上のW₂切断の自然性と変数上のδ両立性から、多項式環上のδ射を判定する。
整数係数では係数側の条件は環準同型の一意性だけで従う。 -/
theorem isDeltaHom_mvPolynomial_of_sectionHom_comp_C
    (D : DeltaStructure p (MvPolynomial σ R)) (E : DeltaStructure p A)
    (f : MvPolynomial σ R →+* A)
    (hC : ((wittTwoMap (p := p) f).comp D.sectionHom).comp MvPolynomial.C =
      (E.sectionHom.comp f).comp MvPolynomial.C)
    (hX : ∀ s, f (D.delta (MvPolynomial.X s)) = E.delta (f (MvPolynomial.X s))) :
    D.IsDeltaHom E f := by
  apply (D.isDeltaHom_iff_sectionHom_comp E f).mpr
  apply MvPolynomial.ringHom_ext' hC
  intro s
  apply TruncatedWittVector.ext
  intro i
  fin_cases i
  · simp only [RingHom.comp_apply, wittTwoMap_coeff]
    change f ((D.sectionHom (MvPolynomial.X s)).coeff 0) =
      (E.sectionHom (f (MvPolynomial.X s))).coeff 0
    rw [D.coeff_zero, E.coeff_zero]
  · simp only [RingHom.comp_apply, wittTwoMap_coeff]
    exact hX s

/-- 任意の多項式δ構造からの環射は、係数と変数上でδと可換ならδ射。
p正則性や非零性を要求せず、W₂切断の二座標を比較する。 -/
theorem isDeltaHom_mvPolynomial (D : DeltaStructure p (MvPolynomial σ R))
    (E : DeltaStructure p A) (f : MvPolynomial σ R →+* A)
    (hC : ∀ r, f (D.delta (MvPolynomial.C r)) = E.delta (f (MvPolynomial.C r)))
    (hX : ∀ s, f (D.delta (MvPolynomial.X s)) = E.delta (f (MvPolynomial.X s))) :
    D.IsDeltaHom E f := by
  apply D.isDeltaHom_mvPolynomial_of_sectionHom_comp_C E f _ hX
  apply RingHom.ext
  intro r
  apply TruncatedWittVector.ext
  intro i
  fin_cases i
  · simp only [RingHom.comp_apply, wittTwoMap_coeff]
    change f ((D.sectionHom (MvPolynomial.C r)).coeff 0) =
      (E.sectionHom (f (MvPolynomial.C r))).coeff 0
    rw [D.coeff_zero, E.coeff_zero]
  · simp only [RingHom.comp_apply, wittTwoMap_coeff]
    exact hC r

end DeltaStructure
end SerrePositivity.BhattScholze
