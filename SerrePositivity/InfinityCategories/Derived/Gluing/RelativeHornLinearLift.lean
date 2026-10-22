module
public import SerrePositivity.InfinityCategories.Derived.Gluing.RelativeHornFaces

/-! 次数別全射な鎖写像に沿う相対ホーンの線形持ち上げ。準同型性は要求しない。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom
open scoped Simplicial
variable {R : Type u} [CommRing R] {D E : Type v}
  [DGCategory R D] [DGCategory R E] {x y : D} {x' y' : E}

lemma dgGluingRelativeHorn_linear_lift
    (φ : homObject R D x y ⟶ homObject R E x' y')
    (hs : ∀ k : ℤ, Function.Surjective (φ.f k)) {n : ℕ} {i : Fin (n + 2)}
    (b : (Λ[n + 1, i] : SSet.{max u v}) ⟶ DGNerve.pinchedHom R D x y)
    (t : (DGNerve.pinchedHom R E x' y') _⦋n + 1⦌)
    (hb : b ≫ pinchedHomChainMap φ = Λ[n + 1, i].ι ≫ SSet.yonedaEquiv.symm t) :
    ∃ s : LinearSimplex R x y (n + 1),
      (∀ j (hji : j ≠ i), LinearData.pullback j.succAboveOrderEmb.toOrderHom s.val =
        HornData.faceData b j hji) ∧ pinchedLinearSimplexMap φ s = toLinearSimplex t := by
  let q : ∀ k : ℤ, k = 1 - ((Finset.univ : Finset (Fin (n + 2))).card : ℤ) →
      GradedHom R x y k := fun k hk =>
    Classical.choose (hs k ((toLinearSimplex t).val.component Finset.univ k
      Finset.univ_nonempty hk))
  let s := dgGluingHornTopSimplex b q
  have hf : ∀ j (hji : j ≠ i), LinearData.pullback j.succAboveOrderEmb.toOrderHom s.val =
      HornData.faceData b j hji := dgGluingHornTopData_face b q
  refine ⟨s, hf, ?_⟩
  apply dgGluingHornSimplex_ext i
  · intro k hk
    change φ.f k ((dgGluingHornTopData b q).component Finset.univ k
      Finset.univ_nonempty hk) = _
    rw [dgGluingHornTopData_top]
    exact Classical.choose_spec (hs k ((toLinearSimplex t).val.component Finset.univ k
      Finset.univ_nonempty hk))
  · apply dgGluingHornData_component_eq_of_faces i
    intro j hji
    change LinearData.pullback j.succAboveOrderEmb.toOrderHom
      (pinchedLinearDataMap φ s.val) = _
    rw [← pinchedLinearDataMap_pullback, hf j hji]
    exact dgGluingRelativeHorn_face_map φ b t hb j hji

end SerrePositivity.InfinityCategories
