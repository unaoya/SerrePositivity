module
public import SerrePositivity.InfinityCategories.Derived.PinchedBoundaryFaceCompatibility

/-! # 全真部分集合の一致から実 pinched 境界の一致へ

概要：鎖写像で写した既知成分を持つ線形単体が、実境界写像を厳密に充填する。
方針：各面の像部分集合は真部分集合なので、成分の一致を面へ引き戻す。
規約：任意の Hom 鎖写像を許す。使われ方：共通実分母による境界充填。
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

/-- 全真部分集合の指定像を保つ線形単体は、実境界の指定像を充填する。 -/
lemma pinchedBoundary_eq_of_proper_components
    (φ : homObject A D x y ⟶ homObject A E x' y') {n : ℕ}
    (b : (∂Δ[n + 1] : SSet.{max u v}) ⟶ DGNerve.pinchedHom A D x y)
    (s : LinearSimplex A x' y' (n + 1))
    (hp : ∀ J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)), J ≠ Finset.univ →
      s.val.component J k hJ hk = φ.f k ((pinchedBoundaryKnownData b).component J k hJ hk)) :
    (∂Δ[n + 1]).ι ≫ SSet.yonedaEquiv.symm s.toPinched = b ≫ pinchedHomChainMap φ := by
  apply SSet.boundary.hom_ext
  intro j
  rw [← Category.assoc, SSet.boundary.ι_ι]
  apply SSet.yonedaEquiv.injective
  rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.apply_symm_apply,
    ← Category.assoc, SSet.yonedaEquiv_comp]
  apply (linearEquiv x' y' n).injective
  change toLinearSimplex (s.toPinched.pullback (SimplexCategory.δ j)) =
    toLinearSimplex (pinchedHomChainMapSimplex φ (SSet.yonedaEquiv (SSet.boundary.ι j ≫ b)))
  rw [toLinearSimplex_pullback, LinearSimplex.toLinearSimplex_toPinched,
    pinchedHomChainMapSimplex_linear]
  apply Subtype.ext
  change LinearData.pullback j.succAboveOrderEmb.toOrderHom s.val =
    pinchedLinearDataMap φ (pinchedBoundaryFaceData b j)
  rw [← pinchedBoundaryKnownData_pullback_face, pinchedLinearDataMap_pullback]
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  change (LinearData.pullback j.succAboveOrderEmb.toOrderHom s.val).component J k hJ hk =
    (LinearData.pullback j.succAboveOrderEmb.toOrderHom
      (pinchedLinearDataMap φ (pinchedBoundaryKnownData b))).component J k hJ hk
  rw [LinearData.pullback_component_of_inj _ _ _ _ _ _ j.succAboveOrderEmb.injective.injOn,
    LinearData.pullback_component_of_inj _ _ _ _ _ _ j.succAboveOrderEmb.injective.injOn]
  exact hp _ _ _ _ (pinchedBoundary_image_ne_univ j J)

end SerrePositivity.InfinityCategories
