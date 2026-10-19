module
public import SerrePositivity.InfinityCategories.Derived.PinchedBoundaryData
public import SerrePositivity.InfinityCategories.Derived.PinchedPrimitiveFilling

/-! # Pinched Hom の実境界の原始元による充填

概要：閉元の原始元作用素から、実際の全境界写像の充填単体を作る。
方針：境界の成分回収、最上位の置換、線形表示と pinched 単体の比較を合成する。
規約：全ての面を厳密に保持する。使われ方：β3 の mapping space の可縮性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {x y : D}

/-- 実際の全境界から構成する線形充填単体。 -/
def pinchedBoundaryLinearFiller {n : ℕ}
    (b : (∂Δ[n + 1] : SSet.{max u v}) ⟶ DGNerve.pinchedHom A D x y)
    (p : ∀ k : ℤ, GradedHom A x y (k + 1) → GradedHom A x y k)
    (hp : ∀ k a, differential A a = 0 → differential A (p k a) = a) :
    LinearSimplex A x y (n + 1) :=
  pinchedPrimitiveFiller (pinchedBoundaryKnownData b) (pinchedBoundaryKnownData_equation b) p hp

/-- 線形充填を任意の面へ制限すると、元の境界の面を厳密に回収する。 -/
lemma pinchedBoundaryLinearFiller_pullback {n : ℕ}
    (b : (∂Δ[n + 1] : SSet.{max u v}) ⟶ DGNerve.pinchedHom A D x y)
    (p : ∀ k : ℤ, GradedHom A x y (k + 1) → GradedHom A x y k)
    (hp : ∀ k a, differential A a = 0 → differential A (p k a) = a)
    (j : Fin (n + 2)) :
    LinearData.pullback j.succAboveOrderEmb.toOrderHom (pinchedBoundaryLinearFiller b p hp).val =
      pinchedBoundaryFaceData b j := by
  rw [← pinchedBoundaryKnownData_pullback_face b j]
  funext t
  rcases t with ⟨⟨J, k⟩, hJ, hk⟩
  change (LinearData.pullback j.succAboveOrderEmb.toOrderHom
    (pinchedBoundaryLinearFiller b p hp).val).component J k hJ hk =
      (LinearData.pullback j.succAboveOrderEmb.toOrderHom
        (pinchedBoundaryKnownData b)).component J k hJ hk
  rw [LinearData.pullback_component_of_inj _ _ _ _ _ _ j.succAboveOrderEmb.injective.injOn,
    LinearData.pullback_component_of_inj _ _ _ _ _ _ j.succAboveOrderEmb.injective.injOn]
  exact pinchedPrimitiveFillerData_proper _ _ _ _ _ _ (pinchedBoundary_image_ne_univ j J)

/-- 線形充填を実際の pinched 単体へ戻す。 -/
def pinchedBoundaryFiller {n : ℕ}
    (b : (∂Δ[n + 1] : SSet.{max u v}) ⟶ DGNerve.pinchedHom A D x y)
    (p : ∀ k : ℤ, GradedHom A x y (k + 1) → GradedHom A x y k)
    (hp : ∀ k a, differential A a = 0 → differential A (p k a) = a) :
    (DGNerve.pinchedHom A D x y) _⦋n + 1⦌ := (pinchedBoundaryLinearFiller b p hp).toPinched

/-- 充填単体の各面は元の境界の面そのもの。 -/
lemma pinchedBoundaryFiller_face {n : ℕ}
    (b : (∂Δ[n + 1] : SSet.{max u v}) ⟶ DGNerve.pinchedHom A D x y)
    (p : ∀ k : ℤ, GradedHom A x y (k + 1) → GradedHom A x y k)
    (hp : ∀ k a, differential A a = 0 → differential A (p k a) = a)
    (j : Fin (n + 2)) :
    (pinchedBoundaryFiller b p hp).pullback (SimplexCategory.δ j) =
      SSet.yonedaEquiv (SSet.boundary.ι j ≫ b) := by
  apply (linearEquiv x y n).injective
  change toLinearSimplex ((pinchedBoundaryFiller b p hp).pullback (SimplexCategory.δ j)) = _
  rw [toLinearSimplex_pullback]
  apply Subtype.ext
  change LinearData.pullback j.succAboveOrderEmb.toOrderHom
    (toLinearData (pinchedBoundaryFiller b p hp)) = pinchedBoundaryFaceData b j
  have he : toLinearData (pinchedBoundaryFiller b p hp) =
      (pinchedBoundaryLinearFiller b p hp).val :=
    congrArg Subtype.val
      (LinearSimplex.toLinearSimplex_toPinched (pinchedBoundaryLinearFiller b p hp))
  rw [he]
  exact pinchedBoundaryLinearFiller_pullback b p hp j

/-- 閉元を全て境界にする作用素があれば、任意の正次元の境界写像を埋められる。 -/
lemma pinchedBoundaryFilling {n : ℕ}
    (b : (∂Δ[n + 1] : SSet.{max u v}) ⟶ DGNerve.pinchedHom A D x y)
    (p : ∀ k : ℤ, GradedHom A x y (k + 1) → GradedHom A x y k)
    (hp : ∀ k a, differential A a = 0 → differential A (p k a) = a) :
    ∃ F : (Δ[n + 1] : SSet.{max u v}) ⟶ DGNerve.pinchedHom A D x y,
      (∂Δ[n + 1]).ι ≫ F = b := by
  refine ⟨SSet.yonedaEquiv.symm (pinchedBoundaryFiller b p hp), ?_⟩
  apply SSet.boundary.hom_ext
  intro j
  rw [← Category.assoc, SSet.boundary.ι_ι]
  apply SSet.yonedaEquiv.injective
  rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.apply_symm_apply]
  exact pinchedBoundaryFiller_face b p hp j

end SerrePositivity.InfinityCategories
