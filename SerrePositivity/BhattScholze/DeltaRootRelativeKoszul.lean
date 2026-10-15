module

public import SerrePositivity.BhattScholze.DeltaRootFiniteKoszulAugmentation
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletionQuasiIso

/-! # 有限根関係と係数側Koszul操作の相対比較

係数側の列は任意であり、p,dの正則性やそのKoszul複体の次数零集中は仮定しない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (b : σ → A) {n : ℕ} (s : Fin n → σ) (hs : Function.Injective s)
variable (N : Type u) [AddCommGroup N] [Module A N]

/-- 根関係の実添加写像に係数側の有限Koszul操作を施した具体的な写像。 -/
def deltaRootFiniteRelativeKoszulAugmentation {m : ℕ} (a : Fin m → A) :
    koszulComplexOn (fun i ↦ MvPolynomial.C (a i))
      ((koszulModuleFunctor (fun j ↦ deltaRootRelationFamily (p := p) b (s j))).obj
        (ModuleCat.of (MvPolynomial σ A) (TensorProduct A (MvPolynomial σ A) N))) ⟶
    koszulComplexOn (fun i ↦ MvPolynomial.C (a i))
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        (ModuleCat.of (MvPolynomial σ A) (TensorProduct A (MvPolynomial σ A ⧸
          Ideal.span (Set.range fun j ↦ deltaRootRelationFamily (p := p) b (s j))) N))) :=
  (koszulFunctor (fun i ↦ MvPolynomial.C (a i))).map
    (deltaRootFiniteKoszulCoefficientAugmentation (p := p) b s hs N)

/-- 係数側の任意有限列での相対添加写像は擬同型。係数列の正則性は不要。 -/
theorem deltaRootFiniteRelativeKoszulAugmentation_quasiIso {m : ℕ} (a : Fin m → A) :
    QuasiIso (deltaRootFiniteRelativeKoszulAugmentation (p := p) b s hs N a) := by
  change QuasiIso ((koszulFunctor (fun i ↦ MvPolynomial.C (a i))).map
    (deltaRootFiniteKoszulCoefficientAugmentation (p := p) b s hs N))
  induction m with
  | zero => exact deltaRootFiniteKoszulCoefficientAugmentation_quasiIso b s hs N
  | succ m ih =>
      let : QuasiIso ((koszulFunctor
          (Fin.init (fun i ↦ MvPolynomial.C (a i)))).map
          (deltaRootFiniteKoszulCoefficientAugmentation (p := p) b s hs N)) := ih (Fin.init a)
      exact DerivedCompletion.scalarConeFunctor_map_quasiIso (MvPolynomial σ A)
        (MvPolynomial.C (a (Fin.last m))) _

/-- 特に係数側のp,dのKoszul操作を伴う実相対比較は擬同型。 -/
theorem deltaRootFiniteRelativeKoszulAugmentation_pd_quasiIso (d : A) :
    QuasiIso (deltaRootFiniteRelativeKoszulAugmentation (p := p) b s hs N ![(p : A), d]) :=
  deltaRootFiniteRelativeKoszulAugmentation_quasiIso b s hs N _

end SerrePositivity.BhattScholze
