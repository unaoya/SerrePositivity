module
public import SerrePositivity.InfinityCategories.Derived.PinchedRelativeBoundaryLifting
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationEquivalence
public import SerrePositivity.InfinityCategories.DGNerve.PinchedKan

/-! # 全射準同型な Hom 鎖写像の写像空間上の自明 Kan fibration

概要：全射準同型な鎖写像は固定対象間の実際の写像空間で同値を与える。
方針：零次元の閉元の持ち上げと正次元の相対境界充填を合成する。
規約：対象上全射性は不要。使われ方：β3 の dg nerve の充満忠実性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D E : Type v}
variable [DGCategory A D] [DGCategory A E] {x y : D} {x' y' : E}

/-- 零次元の目標の pinched 単体も全射準同型な鎖写像に沿って持ち上がる。 -/
lemma pinchedHomChainMap_lift_vertex (φ : homObject A D x y ⟶ homObject A E x' y')
    (hs : ∀ i : ℤ, Function.Surjective (φ.f i)) (hq : QuasiIso φ)
    (t : (DGNerve.pinchedHom A E x' y') _⦋0⦌) :
    ∃ s : (DGNerve.pinchedHom A D x y) _⦋0⦌, (pinchedHomChainMap φ).app _ s = t := by
  have hfull : ∀ J : Finset (Fin 1), J.Nonempty → J = Finset.univ := by
    intro J hJ
    apply Finset.eq_univ_of_forall
    intro i
    obtain ⟨j, hj⟩ := hJ
    simpa only [Subsingleton.elim j i] using hj
  obtain ⟨s, _, hm⟩ := pinchedLinear_relative_simplex_lift φ hs hq
    (0 : LinearData A x y 0)
    (by intro J k hJ hk hne; exact (hne (hfull J hJ)).elim)
    (toLinearSimplex t)
    (by intro J k hJ hk hne; exact (hne (hfull J hJ)).elim)
  refine ⟨s.toPinched, ?_⟩
  apply (linearEquiv x' y' 0).injective
  change toLinearSimplex (pinchedHomChainMapSimplex φ s.toPinched) = toLinearSimplex t
  rw [pinchedHomChainMapSimplex_linear, LinearSimplex.toLinearSimplex_toPinched, hm]

/-- 全 Hom の次数ごと全射な準同型が誘導する実際の写像空間の射は自明 Kan fibration。 -/
lemma pinchedHomChainMap_trivialKanFibration
    (φ : homObject A D x y ⟶ homObject A E x' y')
    (hs : ∀ i : ℤ, Function.Surjective (φ.f i)) (hq : QuasiIso φ) :
    TrivialKanFibration (pinchedHomChainMap φ) := by
  apply (trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro b c sq
  cases n with
  | zero =>
    obtain ⟨s, hs'⟩ := pinchedHomChainMap_lift_vertex φ hs hq (SSet.yonedaEquiv c)
    refine CommSq.HasLift.mk' {
      l := SSet.yonedaEquiv.symm s
      fac_left := SSet.boundary.hom_ext₀
      fac_right := ?_ }
    apply SSet.yonedaEquiv.injective
    simp only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact hs'
  | succ n =>
    have hb : b ≫ pinchedHomChainMap φ = (∂Δ[n + 1]).ι ≫
        SSet.yonedaEquiv.symm (SSet.yonedaEquiv c) := by
      simpa only [Equiv.symm_apply_apply] using sq.w
    obtain ⟨L, hL, hφ⟩ := pinchedHomChainMap_relative_boundary_lift φ hs hq b
      (SSet.yonedaEquiv c) hb
    exact CommSq.HasLift.mk' {
      l := L
      fac_left := hL
      fac_right := by simpa only [Equiv.symm_apply_apply] using hφ }

/-- 写像空間の鎖写像は実際のホモトピー逆を持つ同値。 -/
lemma pinchedHomChainMap_isSimplicialHomotopyEquivalence
    (φ : homObject A D x y ⟶ homObject A E x' y')
    (hs : ∀ i : ℤ, Function.Surjective (φ.f i)) (hq : QuasiIso φ) :
    IsSimplicialHomotopyEquivalence (pinchedHomChainMap φ) := by
  let := pinchedHomChainMap_trivialKanFibration φ hs hq
  exact (isQCatEquivalence_of_trivialKanFibration _).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories
