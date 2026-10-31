module

public import SerrePositivity.CLMST.PerfectoidCokernel
public import SerrePositivity.LengthAlgebra.KoszulModule

/-! # perfectoid 化の余核側の Euler 評価の消去

isogeny の実際の零化冪と最後の元のイデアル所属から零作用を確認し、
負次数の長さの有限性から一般の Euler 消去を適用する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.FinitePresentation R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)

/-- 余核を係数とするKoszul複体のEuler評価を、実際の消去冪と所属条件から消す。 -/
theorem perfectoidizationCokernel_euler_eq_zero
    {J : Ideal S} (lam : NormalizedLength S J) (hfg : J.FG)
    (g : R) (N : ℕ)
    (hN : ∀ x : (Perfectoidization R S p hR) ⧸ (perfectoidizationModuleMap R S p hR).range,
      g ^ N • x = 0)
    {e : ℕ} (z : Fin (e + 1) → S)
    (hJ : J ≤ (Ideal.span (Set.range z)).radical)
    (hz : z (Fin.last e) ∈ Ideal.span (Set.range (Fin.init z)) ⊔
      Ideal.span {(algebraMap R S g) ^ N})
    (lNegative : ∀ q : ℤ, q < 0 →
      lam.len (((koszulModuleFunctor z).obj
        (ModuleCat.of S (PerfectoidizationCokernel R S p hR))).homology q) ≠ ⊤) :
    lambdaEuler lam ((koszulModuleFunctor z).obj
      (ModuleCat.of S (PerfectoidizationCokernel R S p hR))) = 0 :=
  lambdaEuler_koszulModule_eq_zero_of_last_mem_span_sup lam z
    (ModuleCat.of S (PerfectoidizationCokernel R S p hR)) ((algebraMap R S g) ^ N)
    (perfectoidizationCokernel_annihilated R S p hR g N hN) hz
    (isPowTorsion_koszulModuleHomology hfg z hJ _) lNegative

end SerrePositivity.CLMST
