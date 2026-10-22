module
public import SerrePositivity.InfinityCategories.Derived.Gluing.RelativeHornLinearLift
public import SerrePositivity.InfinityCategories.Core.KanFibrationTools

/-! 次数別全射な全 Hom 鎖写像は、実 pinched 空間の Kan fibration を誘導する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
variable {R : Type u} [CommRing R] {D E : Type v}
  [DGCategory R D] [DGCategory R E] {x y : D} {x' y' : E}

lemma dgGluingPinchedChainMap_relative_horn_lift
    (φ : homObject R D x y ⟶ homObject R E x' y')
    (hs : ∀ k : ℤ, Function.Surjective (φ.f k)) {n : ℕ} {i : Fin (n + 2)}
    (b : (Λ[n + 1, i] : SSet.{max u v}) ⟶ DGNerve.pinchedHom R D x y)
    (t : (DGNerve.pinchedHom R E x' y') _⦋n + 1⦌)
    (hb : b ≫ pinchedHomChainMap φ = Λ[n + 1, i].ι ≫ SSet.yonedaEquiv.symm t) :
    ∃ L : (Δ[n + 1] : SSet.{max u v}) ⟶ DGNerve.pinchedHom R D x y,
      Λ[n + 1, i].ι ≫ L = b ∧ L ≫ pinchedHomChainMap φ = SSet.yonedaEquiv.symm t := by
  obtain ⟨s, hf, hm⟩ := dgGluingRelativeHorn_linear_lift φ hs b t hb
  have hfaces : ∀ j (hji : j ≠ i),
      (DGNerve.pinchedHom R D x y).δ j s.toPinched =
        b.app _ (SSet.horn.face i j hji) := by
    intro j hji
    apply (linearEquiv x y n).injective
    change toLinearSimplex (s.toPinched.pullback (SimplexCategory.δ j)) = _
    rw [toLinearSimplex_pullback, LinearSimplex.toLinearSimplex_toPinched]
    exact Subtype.ext (hf j hji)
  refine ⟨SSet.yonedaEquiv.symm s.toPinched, ?_, ?_⟩
  · symm
    apply SSet.horn.hom_ext
    intro j hji
    rw [← hfaces j hji, NatTrans.comp_app]
    rfl
  · apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    apply (linearEquiv x' y' (n + 1)).injective
    change toLinearSimplex (pinchedHomChainMapSimplex φ s.toPinched) = toLinearSimplex t
    rw [pinchedHomChainMapSimplex_linear, LinearSimplex.toLinearSimplex_toPinched, hm]

lemma dgGluingPinchedChainMap_fibration
    (φ : homObject R D x y ⟶ homObject R E x' y')
    (hs : ∀ k : ℤ, Function.Surjective (φ.f k)) :
    Fibration (pinchedHomChainMap φ) := by
  apply fibration_of_hasLiftingProperty_horn
  intro n i
  constructor
  intro b c sq
  have hb : b ≫ pinchedHomChainMap φ = Λ[n + 1, i].ι ≫
      SSet.yonedaEquiv.symm (SSet.yonedaEquiv c) := by
    simpa only [Equiv.symm_apply_apply] using sq.w
  obtain ⟨L, hL, hφ⟩ := dgGluingPinchedChainMap_relative_horn_lift φ hs b
    (SSet.yonedaEquiv c) hb
  exact CommSq.HasLift.mk' {
    l := L
    fac_left := hL
    fac_right := by simpa only [Equiv.symm_apply_apply] using hφ }

end SerrePositivity.InfinityCategories
