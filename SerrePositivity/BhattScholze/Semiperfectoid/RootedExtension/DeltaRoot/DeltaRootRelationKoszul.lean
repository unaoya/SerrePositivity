module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.DeltaRoot.DeltaRootRelationCoefficientQuotient
public import SerrePositivity.CommutativeAlgebra.KoszulResolution
public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.MonicPowerFamilyRelationRegularity
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Logic.Equiv.Option

/-! # 根関係の正則性とKoszul分解

係数環のp正則性・非零性・Noether性を仮定しない。
相対完全正則性や完備化後の平坦性とは区別する。
-/

@[expose] public noncomputable section
universe u v w
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 任意の指定変数の根関係は、係数環に依らず非零因子。 -/
theorem deltaRootRelation_isSMulRegular (b : σ → A) (s : σ) :
    IsSMulRegular (MvPolynomial σ A) (deltaRootRelationFamily (p := p) b s) :=
  monicPowerFamilyRelation_isSMulRegular (Fact.out : p.Prime).ne_zero b s

/-- 一つの根関係の列は弱正則。零環も許す。 -/
theorem deltaRootRelation_singleton_isWeaklyRegular (b : σ → A) (s : σ) :
    RingTheory.Sequence.IsWeaklyRegular (MvPolynomial σ A)
      [deltaRootRelationFamily (p := p) b s] :=
  (RingTheory.Sequence.isWeaklyRegular_singleton_iff _ _).mpr
    (deltaRootRelation_isSMulRegular b s)

/-- 一つの根関係のKoszul複体は、実際の通常商の自由分解。 -/
theorem deltaRootRelation_singleton_isKoszulResolution (b : σ → A) (s : σ) :
    SerrePositivity.IsKoszulResolution
      (fun _ : Fin 1 ↦ deltaRootRelationFamily (p := p) b s) := by
  apply SerrePositivity.isKoszulResolution_of_isWeaklyRegular
  simpa using deltaRootRelation_singleton_isWeaklyRegular (p := p) b s

/-- 任意係数変更後でも、一つの根関係の標準像は非零因子。 -/
theorem deltaRootRelation_map_isSMulRegular {B : Type w} [CommRing B]
    (f : A →+* B) (b : σ → A) (s : σ) :
    IsSMulRegular (MvPolynomial σ B)
      (MvPolynomial.map f (deltaRootRelationFamily (p := p) b s)) := by
  simpa only [deltaRootRelationFamily, map_sub, map_pow, MvPolynomial.map_X,
    MvPolynomial.map_C] using
    deltaRootRelation_isSMulRegular (p := p) (fun t ↦ f (b t)) s

/-- 任意係数変更後の標準根関係のKoszul複体も通常商の分解となる。 -/
theorem deltaRootRelation_map_singleton_isKoszulResolution {B : Type w} [CommRing B]
    (f : A →+* B) (b : σ → A) (s : σ) :
    SerrePositivity.IsKoszulResolution (fun _ : Fin 1 ↦
      MvPolynomial.map f (deltaRootRelationFamily (p := p) b s)) := by
  apply SerrePositivity.isKoszulResolution_of_isWeaklyRegular
  rw [List.ofFn_const, List.replicate_one,
    RingTheory.Sequence.isWeaklyRegular_singleton_iff]
  exact deltaRootRelation_map_isSMulRegular f b s

end SerrePositivity.BhattScholze
