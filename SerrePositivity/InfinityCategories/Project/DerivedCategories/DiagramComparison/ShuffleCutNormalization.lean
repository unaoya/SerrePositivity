module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NormalizedShuffle
public import Mathlib.AlgebraicTopology.DoldKan.Degeneracies

/-!
概要：shuffle の後の AW 切断で、元と異なる二重次数の成分が正規化で消える。
方針：両切断が単射なら次元の不等式から元の切断点に一致する。非単射は退化消滅を使う。
規約：既存の格子路・AW の前半後半・Moore 射影をそのまま使う。
使われ方：HA 1.2.4、G10 の正規化 shuffle→AW 合成の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex AlgebraicTopology AlgebraicTopology.DoldKan
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

/-- 両因子で退化しない AW 切断は元の第一次数に一致する。 -/
theorem shuffleCut_eq_of_mono {p q n : ℕ} (h : p + q = n)
    (s : ShuffleIndex p n) (i : Fin (n + 1))
    [Mono (awFront n i ≫ s.left)] [Mono (awBack n i ≫ s.right h)] : (i : ℕ) = p := by
  have h₁ := SimplexCategory.len_le_of_mono (awFront n i ≫ s.left)
  have h₂ := SimplexCategory.len_le_of_mono (awBack n i ≫ s.right h)
  change (i : ℕ) ≤ p at h₁
  change n - (i : ℕ) ≤ q at h₂
  have := i.isLt
  omega

/-- 異なる切断点では少なくとも一因子が退化する。 -/
theorem shuffleCut_not_mono {p q n : ℕ} (h : p + q = n)
    (s : ShuffleIndex p n) (i : Fin (n + 1)) (hi : (i : ℕ) ≠ p) :
    ¬ Mono (awFront n i ≫ s.left) ∨ ¬ Mono (awBack n i ≫ s.right h) := by
  by_cases h₁ : Mono (awFront n i ≫ s.left)
  · right
    intro h₂
    exact hi (shuffleCut_eq_of_mono h s i)
  · exact Or.inl h₁

/-- 非単射の単体作用素は、元の Moore 射影への合成で消える。 -/
@[reassoc]
theorem degeneracy_comp_mooreProjection (X : SimplicialObject (ModuleCat.{u} ℤ))
    (n : ℕ) {k : SimplexCategory} (θ : ⦋n⦌ ⟶ k) (hθ : ¬ Mono θ) :
    X.map θ.op ≫ (PInftyToNormalizedMooreComplex X).f n = 0 := by
  let hsplit : SplitMono ((inclusionOfMooreComplexMap X).f n) := {
    retraction := (PInftyToNormalizedMooreComplex X).f n
    id := congrArg (fun t => t.f n) (splitMonoInclusionOfMooreComplexMap X).id }
  have := IsSplitMono.mk' hsplit
  apply (cancel_mono ((inclusionOfMooreComplexMap X).f n)).mp
  rw [Category.assoc, ← comp_f,
    PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap, zero_comp]
  exact degeneracy_comp_PInfty X n θ hθ

/-- 元と異なる二重次数への shuffle・切断の正規化成分は零。 -/
theorem shuffleCut_tensor_zero
    (C D : SimplicialObject (ModuleCat.{u} ℤ)) {p q n : ℕ} (h : p + q = n)
    (s : ShuffleIndex p n) (i : Fin (n + 1)) (hi : (i : ℕ) ≠ p) :
    integerTensorMap
      (C.map (awFront n i ≫ s.left).op ≫ (PInftyToNormalizedMooreComplex C).f i)
      (D.map (awBack n i ≫ s.right h).op ≫
        (PInftyToNormalizedMooreComplex D).f (n - i)) = 0 := by
  rcases shuffleCut_not_mono h s i hi with h₁ | h₂
  · rw [degeneracy_comp_mooreProjection C i _ h₁, integerTensorMap_zero_left]
  · rw [degeneracy_comp_mooreProjection D (n - i) _ h₂, integerTensorMap_zero_right]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
