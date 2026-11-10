module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ChainTensorHomotopy

/-!
# 全テンソルへ移したホモトピーの成分

概要：二つの鎖ホモトピーの全テンソルを各二重次数の実テンソル写像へ展開する。
方針：標準包含と双関手ホモトピーの計算公式を使う。
規約：KST Construction A.5、水平成分の符号は1、垂直成分は (−1)^p。
使われ方：Moore 収縮のテンソルの自然性を成分ごとに検証する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory HomologicalComplex

/-- 概要：全テンソルのホモトピーの標準包含上の二つの実成分。
方針：第一・第二変数のホモトピーの降下写像を評価する。
規約：KST A.5、ℕ 全次数で一段上の成分。
使われ方：テンソルへ移した収縮の自然性と外部群同変性。 -/
lemma ι_chainIntegerTensorHomotopy
    {K K' L L' : ChainComplex (ModuleCat.{u} ℤ) ℕ}
    {f f' : K ⟶ K'} {g g' : L ⟶ L'} (h₁ : Homotopy f f') (h₂ : Homotopy g g')
    (p q n : ℕ) (h : p + q = n) :
    ιMapBifunctor K L _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor (.down ℕ) p q n h ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorHomotopy h₁ h₂).hom n (n + 1) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap (h₁.hom p (p + 1)) (g.f q) ≫
        ιMapBifunctor K' L' _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor (.down ℕ) (p + 1) q (n + 1) (by change (p + 1) + q = n + 1; omega) +
      (-1 : ℤ) ^ p •
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap (f'.f p) (h₂.hom q (q + 1)) ≫
          ιMapBifunctor K' L' _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor (.down ℕ) p (q + 1) (n + 1) (by change p + (q + 1) = n + 1; omega)) := by
  change _ ≫ (mapBifunctorMapHomotopy.hom₁ h₁ g _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor (.down ℕ) n (n + 1) +
    mapBifunctorMapHomotopy.hom₂ f' h₂ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor (.down ℕ) n (n + 1)) = _
  rw [Preadditive.comp_add,
    mapBifunctorMapHomotopy.ιMapBifunctor_hom₁ h₁ g _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor (.down ℕ)
      (p + 1) p q n (n + 1) h (ChainComplex.prev ℕ p),
    mapBifunctorMapHomotopy.ιMapBifunctor_hom₂ f' h₂ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor (.down ℕ)
      p (q + 1) q n (n + 1) h (ChainComplex.prev ℕ q)]
  rw [ιMapBifunctorOrZero_eq K' L' _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor (.down ℕ)
      (p + 1) q (n + 1) (by change (p + 1) + q = n + 1; omega),
    ιMapBifunctorOrZero_eq K' L' _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor (.down ℕ)
      p (q + 1) (n + 1) (by change p + (q + 1) = n + 1; omega)]
  have he₁ : ComplexShape.ε₁ (.down ℕ) (.down ℕ) (.down ℕ) (p + 1, q) = 1 := rfl
  have he₂ : ComplexShape.ε₂ (.down ℕ) (.down ℕ) (.down ℕ) (p, q + 1) = (-1 : ℤˣ) ^ p := rfl
  rw [he₁, one_smul, he₂, Units.smul_def]
  simp only [Units.val_pow_eq_pow_val, Units.coe_neg_one]
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorRight]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap (h₁.hom p (p + 1)) (𝟙 _) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap (𝟙 _) (g.f q) ≫ _ +
    (-1 : ℤ) ^ p • (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap (f'.f p) (𝟙 _) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap (𝟙 _) (h₂.hom q (q + 1)) ≫ _) = _
  simp only [← Category.assoc]
  simp only [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap_comp, Category.comp_id, Category.id_comp,
    Preadditive.zsmul_comp]

end SerrePositivity.KST.ProExcision
