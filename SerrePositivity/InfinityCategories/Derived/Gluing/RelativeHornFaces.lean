module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HornPrescribedTopSimplex
public import SerrePositivity.InfinityCategories.Derived.Gluing.HornSimplexExt
public import SerrePositivity.InfinityCategories.Derived.PinchedChainMapComposition

/-! 相対ホーンの可換条件を、利用可能な全ての線形面へ移す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom
open scoped Simplicial
variable {R : Type u} [CommRing R] {D E : Type v}
  [DGCategory R D] [DGCategory R E] {x y : D} {x' y' : E}

lemma dgGluingRelativeHorn_face_map
    (φ : homObject R D x y ⟶ homObject R E x' y') {n : ℕ} {i : Fin (n + 2)}
    (b : (Λ[n + 1, i] : SSet.{max u v}) ⟶ DGNerve.pinchedHom R D x y)
    (t : (DGNerve.pinchedHom R E x' y') _⦋n + 1⦌)
    (hb : b ≫ pinchedHomChainMap φ = Λ[n + 1, i].ι ≫ SSet.yonedaEquiv.symm t)
    (j : Fin (n + 2)) (hji : j ≠ i) :
    pinchedLinearDataMap φ (HornData.faceData b j hji) =
      LinearData.pullback j.succAboveOrderEmb.toOrderHom (toLinearSimplex t).val := by
  have he := congrArg (fun f => f.app _ (SSet.horn.face i j hji)) hb
  change pinchedHomChainMapSimplex φ (b.app _ (SSet.horn.face i j hji)) =
    t.pullback (SimplexCategory.δ j) at he
  have hh := congrArg (fun s => (toLinearSimplex s).val) he
  rw [pinchedHomChainMapSimplex_linear, toLinearSimplex_pullback] at hh
  exact hh

lemma dgGluingHornTopSimplex_face {n : ℕ} {i : Fin (n + 2)}
    (b : (Λ[n + 1, i] : SSet.{max u v}) ⟶ DGNerve.pinchedHom R D x y)
    (q : ∀ k : ℤ, k = 1 - ((Finset.univ : Finset (Fin (n + 2))).card : ℤ) →
      GradedHom R x y k) (j : Fin (n + 2)) (hji : j ≠ i) :
    (DGNerve.pinchedHom R D x y).δ j (dgGluingHornTopSimplex b q).toPinched =
      b.app _ (SSet.horn.face i j hji) := by
  apply (linearEquiv x y n).injective
  change toLinearSimplex ((dgGluingHornTopSimplex b q).toPinched.pullback
    (SimplexCategory.δ j)) = _
  rw [toLinearSimplex_pullback, LinearSimplex.toLinearSimplex_toPinched]
  exact Subtype.ext (dgGluingHornTopData_face b q j hji)

end SerrePositivity.InfinityCategories
