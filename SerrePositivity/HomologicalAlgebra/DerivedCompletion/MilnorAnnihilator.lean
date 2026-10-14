module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.MilnorSequence
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Milnor短完全列に沿う一様零化

塔の隣接する二次数のホモロジーをそれぞれr,sが一様に消せば、
ホモトピー逆極限のホモロジーをr*sが消す。lim¹の消滅は仮定しない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]
    (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (t : ∀ n, K (n + 1) ⟶ K n)

/-- 全段のホモロジーを消す元は、同じ次数のlim¹も消す。 -/
theorem complexTowerHomologyLimOne_annihilated (i : ℤ) (s : R)
    (hs : ∀ n, ∀ x : (K n).homology i, s • x = 0)
    (x : complexTowerHomologyLimOne R K t i) : s • x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    change Submodule.Quotient.mk (s • x) = (0 : complexTowerHomologyLimOne R K t i)
    have hx : s • x = 0 := by
      funext n
      exact hs n (x n)
    rw [hx]
    rfl

/-- 全段のホモロジーを消す元は、通常の逆極限も消す。 -/
theorem complexTowerHomologyLimit_annihilated (i : ℤ) (r : R)
    (hr : ∀ n, ∀ x : (K n).homology i, r • x = 0)
    (x : moduleTowerLimit R (fun n ↦ (K n).homology i)
      (fun n ↦ (HomologicalComplex.homologyMap (t n) i).hom)) : r • x = 0 := by
  apply Subtype.ext
  funext n
  exact hr n (x.val n)

/-- Milnor列の両端の一様零化から、中項を積で零化する。 -/
theorem complexTowerHomotopyLimit_homology_annihilated (i : ℤ) (r s : R)
    (hr : ∀ n, ∀ x : (K n).homology i, r • x = 0)
    (hs : ∀ n, ∀ x : (K n).homology (i - 1), s • x = 0)
    (x : (complexTowerHomotopyLimit R K t).homology i) : (r * s) • x = 0 := by
  have hx : complexTowerMilnorProjection R K t i (r • x) = 0 := by
    rw [map_smul]
    exact complexTowerHomologyLimit_annihilated R K t i r hr _
  have hex := (ShortComplex.moduleCat_exact_iff _).mp
    (complexTowerMilnorSequence_shortExact R K t i).exact
  change ∀ z, complexTowerMilnorProjection R K t i z = 0 →
    ∃ y, complexTowerMilnorInclusion R K t i y = z at hex
  obtain ⟨y, hy⟩ := hex (r • x) hx
  have hyzero : s • y = 0 := complexTowerHomologyLimOne_annihilated R K t (i - 1) s hs y
  rw [mul_comm r s, mul_smul, ← hy, ← map_smul, hyzero, map_zero]

/-- 同じgᴺが隣接二次数の全段を消せば、holimのホモロジーをg²ᴺが消す。 -/
theorem complexTowerHomotopyLimit_homology_pow_annihilated (i : ℤ) (g : R) (N : ℕ)
    (h : ∀ n, (∀ x : (K n).homology i, g ^ N • x = 0) ∧
      (∀ x : (K n).homology (i - 1), g ^ N • x = 0))
    (x : (complexTowerHomotopyLimit R K t).homology i) : g ^ (2 * N) • x = 0 := by
  have hp : g ^ (2 * N) = g ^ N * g ^ N := by rw [two_mul, pow_add]
  rw [hp]
  exact complexTowerHomotopyLimit_homology_annihilated R K t i _ _
    (fun n ↦ (h n).1) (fun n ↦ (h n).2) x

/-- holimとのホモロジー比較が与えられた対象にも同じ一様指数を移す。 -/
theorem homology_pow_annihilated_of_equiv_homotopyLimit
    (C : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ)
    (e : C.homology i ≃ₗ[R] (complexTowerHomotopyLimit R K t).homology i)
    (g : R) (N : ℕ)
    (h : ∀ n, (∀ x : (K n).homology i, g ^ N • x = 0) ∧
      (∀ x : (K n).homology (i - 1), g ^ N • x = 0))
    (x : C.homology i) : g ^ (2 * N) • x = 0 := by
  apply e.injective
  rw [map_smul, map_zero]
  exact complexTowerHomotopyLimit_homology_pow_annihilated R K t i g N h (e x)

/-- 実導来圏のholimとの比較同型を通じた、一様指数の移送。
比較同型自体は引数であり、導来完備性からの標準比較をこの補題の仮定に隠さない。 -/
theorem derived_homology_pow_annihilated_of_iso_homotopyLimit
    (C : ConcreteDerivedCategory R)
    (e : C ≅ complexTowerHomotopyLimitObject R K t) (i : ℤ) (g : R) (N : ℕ)
    (h : ∀ n, (∀ x : (K n).homology i, g ^ N • x = 0) ∧
      (∀ x : (K n).homology (i - 1), g ^ N • x = 0))
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj C) :
    g ^ (2 * N) • x = 0 := by
  let E := (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso e ≪≫
    (DerivedCategory.homologyFunctorFactors _ i).app (complexTowerHomotopyLimit R K t)
  apply E.toLinearEquiv.injective
  rw [map_smul, map_zero]
  exact complexTowerHomotopyLimit_homology_pow_annihilated R K t i g N h (E.hom x)

end SerrePositivity.DerivedCompletion
