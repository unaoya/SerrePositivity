module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.AWRightAugmentationCut
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NormalizedAlexanderWhitney

/-!
概要：Moore 正規化後も、右増大写像との合成は最後の切断に帰着する。
方針：二因子の射影と右の写像を合成し、非正規化AWの零次切断則を使う。
規約：包含とPInfty射影を保持する。正規化模型を取り替えない。
使われ方：HA 1.2.4、IS-W2 A05a、前提計算枠2。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex AlgebraicTopology AlgebraicTopology.DoldKan
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (C D : SimplicialObject (ModuleCat.{u} ℤ))
variable {L : ChainComplex (ModuleCat.{u} ℤ) ℕ}

/-- 元のMoore正規化AWの右零次成分は、最後の切断と指定射影で計算できる。 -/
theorem normalizedAlexanderWhitney_right_zero_degree
    (g : (normalizedMooreComplex _).obj D ⟶ L)
    (hg : ∀ k : ℕ, k ≠ 0 → g.f k = 0) (n : ℕ) :
    (normalizedAlexanderWhitney C D ≫ chainIntegerTensorMap (𝟙 _) g).f n =
      (inclusionOfMooreComplexMap (simplicialIntegerTensor C D)).f n ≫
        integerTensorMap ((PInftyToNormalizedMooreComplex C).f n)
          (D.map (awBack n (Fin.last n)).op ≫
            (PInftyToNormalizedMooreComplex D ≫ g).f (n - n)) ≫
        ιMapBifunctor ((normalizedMooreComplex _).obj C) L integerTensorBifunctor
          (.down ℕ) n (n - n) n (awDegrees n (Fin.last n)) := by
  have hg' : ∀ k : ℕ, k ≠ 0 → (PInftyToNormalizedMooreComplex D ≫ g).f k = 0 := by
    intro k hk
    simp only [comp_f, hg k hk, CategoryTheory.Limits.comp_zero]
  have hfront : awFront n (Fin.last n) = 𝟙 _ := by
    apply SimplexCategory.Hom.ext
    ext i
    rfl
  dsimp only [normalizedAlexanderWhitney]
  simp only [Category.assoc]
  rw [← chainIntegerTensorMap_comp]
  simp only [Category.comp_id, comp_f]
  rw [show (alexanderWhitney C D).f n = alexanderWhitneyApp C D n from rfl,
    ← Category.assoc, Category.assoc,
    alexanderWhitneyApp_right_zero_degree C D _ _ hg']
  dsimp only [alexanderWhitneySummand]
  rw [Category.assoc, ι_chainIntegerTensorMap]
  rw [← Category.assoc (integerTensorMap _ _) (integerTensorMap _ _) _,
    ← integerTensorMap_comp]
  simp only [hfront, op_id]
  erw [C.map_id, Category.id_comp]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
