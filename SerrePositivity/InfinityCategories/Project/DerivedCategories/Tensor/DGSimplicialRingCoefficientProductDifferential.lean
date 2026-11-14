module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGSimplicialRingMooreProductDifferential
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGSimplicialRingCochainUnit
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
local notation "E" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.integerCoefficientModuleFunctor
lemma integerCoefficientTensorComparison_precomp
    {M M' Q Q' K : ModuleCat.{u} ℤ} (f : M ⟶ M') (g : Q ⟶ Q')
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensor M' Q' ⟶ K) :
    ((E).map f ⊗ₘ (E).map g) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.integerCoefficientTensorComparison M' Q' ≫ (E).map h =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.integerCoefficientTensorComparison M Q ≫ (E).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap f g ≫ h) := by
  simpa only [Functor.map_comp, Category.assoc] using!
    congrArg (fun ψ ↦ ψ ≫ (E).map h) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.integerCoefficientTensorComparison_naturality f g)

def simplicialRingCoefficientMooreBidegree (p q n : ℕ) (h : p + q = n) :
    (E).obj ((N).X p) ⊗ (E).obj ((N).X q) ⟶ (E).obj ((N).X n) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.integerCoefficientTensorComparison _ _ ≫
    (E).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingMooreMultiplicationBidegree A p q n h)
lemma simplicialRingCoefficientMooreBidegree_post_d (p q s n : ℕ) (h : p + q = s) :
    simplicialRingCoefficientMooreBidegree A p q s h ≫ (E).map ((N).d s n) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.integerCoefficientTensorComparison ((N).X p) ((N).X q) ≫ (E).map
      (ιMapBifunctor N N _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor (.down ℕ) p q s h ≫
        mapBifunctor.D₁ N N _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor (.down ℕ) s n ≫ (mu).f n) +
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.integerCoefficientTensorComparison ((N).X p) ((N).X q) ≫ (E).map
      (ιMapBifunctor N N _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor (.down ℕ) p q s h ≫
        mapBifunctor.D₂ N N _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor (.down ℕ) s n ≫ (mu).f n) := by
  dsimp only [simplicialRingCoefficientMooreBidegree]
  rw [Category.assoc, ← Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingMooreMultiplicationBidegree_d,
    Functor.map_add, Preadditive.comp_add]
lemma simplicialRingCoefficientMooreBidegree_succ_succ (p q : ℕ) :
    simplicialRingCoefficientMooreBidegree A (p + 1) (q + 1) ((p + q + 1) + 1)
        (by omega) ≫ (E).map ((N).d ((p + q + 1) + 1) (p + q + 1)) =
    ((E).map ((N).d (p + 1) p) ⊗ₘ 𝟙 ((E).obj ((N).X (q + 1)))) ≫
      simplicialRingCoefficientMooreBidegree A p (q + 1) (p + q + 1) (by omega) +
    (-1 : ℤ) ^ (p + 1) •
      ((𝟙 ((E).obj ((N).X (p + 1))) ⊗ₘ (E).map ((N).d (q + 1) q)) ≫
        simplicialRingCoefficientMooreBidegree A (p + 1) q (p + q + 1) (by omega)) := by
  dsimp only [simplicialRingCoefficientMooreBidegree]
  rw [Category.assoc, ← Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingMooreMultiplication_succ_succ,
    Functor.map_add, Functor.map_zsmul, Preadditive.comp_add, Preadditive.comp_zsmul]
  congr 1
  · simpa only [Functor.map_id] using!
      (integerCoefficientTensorComparison_precomp ((N).d (p + 1) p) (𝟙 ((N).X (q + 1)))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingMooreMultiplicationBidegree A p (q + 1) (p + q + 1) (by omega))).symm
  · congr 1
    simpa only [Functor.map_id] using!
      (integerCoefficientTensorComparison_precomp (𝟙 ((N).X (p + 1))) ((N).d (q + 1) q)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingMooreMultiplicationBidegree A (p + 1) q (p + q + 1) (by omega))).symm
lemma simplicialRingCoefficientMooreBidegree_zero_succ (q : ℕ) :
    simplicialRingCoefficientMooreBidegree A 0 (q + 1) (q + 1) (by omega) ≫
        (E).map ((N).d (q + 1) q) =
    (𝟙 ((E).obj ((N).X 0)) ⊗ₘ (E).map ((N).d (q + 1) q)) ≫
      simplicialRingCoefficientMooreBidegree A 0 q q (by omega) := by
  dsimp only [simplicialRingCoefficientMooreBidegree]
  rw [Category.assoc, ← Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingMooreMultiplication_zero_succ]
  simpa only [Functor.map_id] using!
    (integerCoefficientTensorComparison_precomp (𝟙 ((N).X 0)) ((N).d (q + 1) q)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingMooreMultiplicationBidegree A 0 q q (by omega))).symm

lemma simplicialRingCoefficientMooreBidegree_succ_zero (p : ℕ) :
    simplicialRingCoefficientMooreBidegree A (p + 1) 0 (p + 1) (by omega) ≫
        (E).map ((N).d (p + 1) p) =
    ((E).map ((N).d (p + 1) p) ⊗ₘ 𝟙 ((E).obj ((N).X 0))) ≫
      simplicialRingCoefficientMooreBidegree A p 0 p (by omega) := by
  dsimp only [simplicialRingCoefficientMooreBidegree]
  rw [Category.assoc, ← Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingMooreMultiplication_succ_zero]
  simpa only [Functor.map_id] using!
    (integerCoefficientTensorComparison_precomp ((N).d (p + 1) p) (𝟙 ((N).X 0))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingMooreMultiplicationBidegree A p 0 p (by omega))).symm
end SerrePositivity.InfinityCategories.Project.DerivedCategories
