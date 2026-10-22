module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorDoubleConeOverSimplex

/-!
概要：終端 X 上の実二重 cone 単体の全自然性と、元の cone への厳密な射影を証明する。
方針：標準 join の自然性を同じ二重 cone の全自然性へ戻し、前面を回収する。
規約：同じ元の図式全体を保持する。使われ方：slice 内の大域 cone の組立。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories DGNerve
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorDoubleConeOverSimplex_naturality {n m : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    normalizedTensorDoubleConeOverSimplex A X Y ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) =
      (sliceOver (normalizedTensorConePoint A X)).map
        (SimplexCategory.mkHom (prependOrderHom θ.toOrderHom)).op
        (normalizedTensorDoubleConeOverSimplex A X Y c) := by
  apply Subtype.ext
  change (joinStdSimplexIso (m + 1) 0).hom ≫
      (SSet.yonedaEquiv (X := dgNerve A (Complex A))).symm
        (normalizedTensorDoubleConeSimplex A X Y ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)) =
    joinMap (SSet.stdSimplex.map (SimplexCategory.mkHom (prependOrderHom θ.toOrderHom)))
      (𝟙 Δ[0]) ≫ ((joinStdSimplexIso (n + 1) 0).hom ≫
        (SSet.yonedaEquiv (X := dgNerve A (Complex A))).symm
          (normalizedTensorDoubleConeSimplex A X Y c))
  rw [← Category.assoc, joinStdSimplexIso_rightPoint_naturality, Category.assoc,
    SSet.yonedaEquiv_symm_naturality_left]
  have hn := (normalizedTensorDoubleConeSimplex_pullback_map A X Y c θ).symm
  exact congrArg (fun s : Simplex A (Complex A) (m + 2) =>
    (joinStdSimplexIso (m + 1) 0).hom ≫
      (SSet.yonedaEquiv (X := dgNerve A (Complex A))).symm s) hn

lemma normalizedTensorDoubleConeOverSimplex_projection {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) :
    (sliceOverProjection (normalizedTensorConePoint A X)).app (Opposite.op ⦋n + 1⦌)
      (normalizedTensorDoubleConeOverSimplex A X Y c) = normalizedTensorConeSimplex A X Y c := by
  change SSet.yonedaEquiv (joinInl (Δ[n + 1] : SSet.{u + 1}) Δ[0] ≫
    ((joinStdSimplexIso (n + 1) 0).hom ≫
      (SSet.yonedaEquiv (X := dgNerve A (Complex A))).symm
        (normalizedTensorDoubleConeSimplex A X Y c))) = _
  rw [← Category.assoc, joinStdSimplexIso_rightPoint_inl,
    ← SSet.yonedaEquiv_naturality, Equiv.apply_symm_apply]
  exact normalizedTensorDoubleConeSimplex_front A X Y c

end SerrePositivity.EInfinity.ComplexLimits
