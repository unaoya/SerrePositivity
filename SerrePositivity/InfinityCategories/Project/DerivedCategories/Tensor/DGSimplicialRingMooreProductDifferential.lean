module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGSimplicialRingNormalizedDegreeLaws
/-!
概要：元の Moore 乗法の実微分を係数移送後の標準 tensor に比較する。
方針：元の鎖写像の二微分項、実 tensor 同型と整数倍の自然性を使う。
規約：零次数境界と元の Koszul 符号を保持する。使われ方：β5(g)。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory HomologicalComplex
variable (A : SimplicialObject RingCat.{u})
local notation "N" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedChains A
local notation "mu" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedMultiplication A
def simplicialRingMooreMultiplicationBidegree (p q n : ℕ) (h : p + q = n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensor ((N).X p) ((N).X q) ⟶ (N).X n :=
  ιMapBifunctor N N _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor (.down ℕ) p q n h ≫ (mu).f n
lemma simplicialRingMooreMultiplicationBidegree_d (p q s n : ℕ) (h : p + q = s) :
    simplicialRingMooreMultiplicationBidegree A p q s h ≫ (N).d s n =
      ιMapBifunctor N N _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor (.down ℕ) p q s h ≫
        mapBifunctor.D₁ N N _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor (.down ℕ) s n ≫ (mu).f n +
      ιMapBifunctor N N _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor (.down ℕ) p q s h ≫
        mapBifunctor.D₂ N N _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor (.down ℕ) s n ≫ (mu).f n := by
  dsimp only [simplicialRingMooreMultiplicationBidegree]
  rw [Category.assoc, (mu).comm s n, mapBifunctor.d_eq,
    Preadditive.add_comp, Preadditive.comp_add]
lemma simplicialRingMooreMultiplication_D₁_succ {p q n : ℕ} (h : p + q = n) :
    ιMapBifunctor N N _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor (.down ℕ)
        (p + 1) q (n + 1) (by change (p + 1) + q = n + 1; omega) ≫
      mapBifunctor.D₁ N N _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor (.down ℕ) (n + 1) n ≫ (mu).f n =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap ((N).d (p + 1) p) (𝟙 ((N).X q)) ≫
      simplicialRingMooreMultiplicationBidegree A p q n h := by
  rw [← Category.assoc, mapBifunctor.ι_D₁,
    mapBifunctor.d₁_eq _ _ _ _ (i₁ := p + 1) (i₁' := p) rfl q n h]
  have he : ComplexShape.ε₁ (.down ℕ) (.down ℕ) (.down ℕ) (p + 1, q) = 1 := rfl
  rw [he, one_smul]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap ((N).d (p + 1) p) (𝟙 _) ≫ _) ≫ _ = _
  rfl
lemma simplicialRingMooreMultiplication_D₁_zero {q n s : ℕ} (h : 0 + q = s) :
    ιMapBifunctor N N _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor (.down ℕ) 0 q s h ≫
      mapBifunctor.D₁ N N _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor (.down ℕ) s n ≫ (mu).f n = 0 := by
  rw [← Category.assoc, mapBifunctor.ι_D₁,
    mapBifunctor.d₁_eq_zero _ _ _ _ 0 q n (by simp), Limits.zero_comp]
lemma simplicialRingMooreMultiplication_D₂_succ {p q n : ℕ} (h : p + q = n) :
    ιMapBifunctor N N _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor (.down ℕ)
        p (q + 1) (n + 1) (by change p + (q + 1) = n + 1; omega) ≫
      mapBifunctor.D₂ N N _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor (.down ℕ) (n + 1) n ≫ (mu).f n =
    (-1 : ℤ) ^ p • (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap (𝟙 ((N).X p)) ((N).d (q + 1) q) ≫
      simplicialRingMooreMultiplicationBidegree A p q n h) := by
  rw [← Category.assoc, mapBifunctor.ι_D₂,
    mapBifunctor.d₂_eq _ _ _ _ p (i₂ := q + 1) (i₂' := q) rfl n h]
  have he : ComplexShape.ε₂ (.down ℕ) (.down ℕ) (.down ℕ) (p, q + 1) =
      (-1 : ℤˣ) ^ p := rfl
  rw [he, Units.smul_def]
  change ((-1 : ℤ) ^ p • (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap (𝟙 _) ((N).d (q + 1) q) ≫ _)) ≫ _ = _
  rw [Preadditive.zsmul_comp]
  rfl
lemma simplicialRingMooreMultiplication_D₂_zero {p n s : ℕ} (h : p + 0 = s) :
    ιMapBifunctor N N _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor (.down ℕ) p 0 s h ≫
      mapBifunctor.D₂ N N _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor (.down ℕ) s n ≫ (mu).f n = 0 := by
  rw [← Category.assoc, mapBifunctor.ι_D₂,
    mapBifunctor.d₂_eq_zero _ _ _ _ p 0 n (by simp), Limits.zero_comp]
lemma simplicialRingMooreMultiplicationBidegree_naturality
    {A B : SimplicialObject RingCat.{u}} (f : A ⟶ B)
    (p q n : ℕ) (h : p + q = n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedMap f).f p)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedMap f).f q) ≫
      simplicialRingMooreMultiplicationBidegree B p q n h =
    simplicialRingMooreMultiplicationBidegree A p q n h ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedMap f).f n := by
  have hc := congrArg (fun ψ ↦
    ιMapBifunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedChains A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedChains A)
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor (.down ℕ) p q n h ≫ ψ.f n)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedMultiplication_naturality f)
  simpa only [simplicialRingMooreMultiplicationBidegree, comp_f,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ι_chainIntegerTensorMap] using! hc

lemma simplicialRingMooreMultiplication_succ_succ (p q : ℕ) :
    simplicialRingMooreMultiplicationBidegree A (p + 1) (q + 1) ((p + q + 1) + 1)
        (by omega) ≫ (N).d ((p + q + 1) + 1) (p + q + 1) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap ((N).d (p + 1) p) (𝟙 ((N).X (q + 1))) ≫
      simplicialRingMooreMultiplicationBidegree A p (q + 1) (p + q + 1) (by omega) +
    (-1 : ℤ) ^ (p + 1) •
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap (𝟙 ((N).X (p + 1))) ((N).d (q + 1) q) ≫
        simplicialRingMooreMultiplicationBidegree A (p + 1) q (p + q + 1) (by omega)) := by
  rw [simplicialRingMooreMultiplicationBidegree_d,
    simplicialRingMooreMultiplication_D₁_succ A (by omega),
    simplicialRingMooreMultiplication_D₂_succ A (by omega)]
lemma simplicialRingMooreMultiplication_zero_succ (q : ℕ) :
    simplicialRingMooreMultiplicationBidegree A 0 (q + 1) (q + 1) (by omega) ≫
        (N).d (q + 1) q =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap (𝟙 ((N).X 0)) ((N).d (q + 1) q) ≫
      simplicialRingMooreMultiplicationBidegree A 0 q q (by omega) := by
  rw [simplicialRingMooreMultiplicationBidegree_d,
    simplicialRingMooreMultiplication_D₁_zero,
    simplicialRingMooreMultiplication_D₂_succ A (by omega)]
  simp only [pow_zero, one_smul, zero_add]
lemma simplicialRingMooreMultiplication_succ_zero (p : ℕ) :
    simplicialRingMooreMultiplicationBidegree A (p + 1) 0 (p + 1) (by omega) ≫
        (N).d (p + 1) p =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap ((N).d (p + 1) p) (𝟙 ((N).X 0)) ≫
      simplicialRingMooreMultiplicationBidegree A p 0 p (by omega) := by
  rw [simplicialRingMooreMultiplicationBidegree_d,
    simplicialRingMooreMultiplication_D₁_succ A (by omega),
    simplicialRingMooreMultiplication_D₂_zero]
  simp only [add_zero]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
