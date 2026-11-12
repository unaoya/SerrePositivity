module
public import SerrePositivity.KST.ProExcision.ChainIntervalEvaluation

/-!
# 全テンソル鎖区間の二つの微分と評価

概要：区間評価の前の全テンソルの水平・垂直微分を各二重次数で計算する。
方針：全複体の標準包含の微分公式と区間評価の降下公式を合成する。
規約：KST Definition A.3、Construction A.5、垂直微分の符号は第一因子の次数。
使われ方：頂点・辺・自明な高次の三場合で鎖写像性を証明する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory HomologicalComplex
variable {K L : ChainComplex (ModuleCat.{u} ℤ) ℕ} {f g : K ⟶ L} (H : Homotopy f g)

/-- 概要：正の第一因子の水平微分の後の評価は微分と小さい二重次数の評価の合成。
方針：水平微分の標準包含での公式を使う。
規約：KST A.3・A.5、水平符号は1。
使われ方：区間評価の鎖写像性の水平部分。 -/
lemma chainInterval_ι_D₁_succ {p q n : ℕ} (h : p + q = n) :
    ιMapBifunctor K integerChainInterval _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor (.down ℕ)
        (p + 1) q (n + 1) (by change (p + 1) + q = n + 1; omega) ≫
      mapBifunctor.D₁ K integerChainInterval _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor (.down ℕ) (n + 1) n ≫
      chainHomotopyIntervalApp H n =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap (K.d (p + 1) p) (𝟙 (integerChainInterval.X q)) ≫
      chainHomotopyIntervalBidegree H p q n h := by
  rw [← Category.assoc, mapBifunctor.ι_D₁,
    mapBifunctor.d₁_eq _ _ _ _ (i₁ := p + 1) (i₁' := p) rfl q n h]
  have he : ComplexShape.ε₁ (.down ℕ) (.down ℕ) (.down ℕ) (p + 1, q) = 1 := rfl
  rw [he, one_smul]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap (K.d (p + 1) p) (𝟙 _) ≫ _) ≫ _ = _
  rw [Category.assoc, ι_chainHomotopyIntervalApp]

/-- 概要：第一因子が零次なら水平微分の後の評価は零。
方針：零次からの水平微分がないことを使う。
規約：KST A.3・A.5。使われ方：辺の評価の第一因子の零次。 -/
lemma chainInterval_ι_D₁_zero {q n s : ℕ} (h : 0 + q = s) :
    ιMapBifunctor K integerChainInterval _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor (.down ℕ) 0 q s h ≫
      mapBifunctor.D₁ K integerChainInterval _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor (.down ℕ) s n ≫
      chainHomotopyIntervalApp H n = 0 := by
  rw [← Category.assoc, mapBifunctor.ι_D₁,
    mapBifunctor.d₁_eq_zero _ _ _ _ 0 q n (by simp), Limits.zero_comp]

/-- 概要：正の区間次数の垂直微分の後の評価は区間の微分と小さい評価の符号付き合成。
方針：垂直微分の標準包含での公式を使う。
規約：KST A.3・A.5、符号は (−1)^p。
使われ方：辺の境界と二つの端点の差の接続。 -/
lemma chainInterval_ι_D₂_succ {p q n : ℕ} (h : p + q = n) :
    ιMapBifunctor K integerChainInterval _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor (.down ℕ)
        p (q + 1) (n + 1) (by change p + (q + 1) = n + 1; omega) ≫
      mapBifunctor.D₂ K integerChainInterval _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor (.down ℕ) (n + 1) n ≫
      chainHomotopyIntervalApp H n =
    (-1 : ℤ) ^ p • (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap (𝟙 (K.X p)) (integerChainInterval.d (q + 1) q) ≫
      chainHomotopyIntervalBidegree H p q n h) := by
  rw [← Category.assoc, mapBifunctor.ι_D₂,
    mapBifunctor.d₂_eq _ _ _ _ p (i₂ := q + 1) (i₂' := q) rfl n h]
  have he : ComplexShape.ε₂ (.down ℕ) (.down ℕ) (.down ℕ) (p, q + 1) = (-1 : ℤˣ) ^ p := rfl
  rw [he, Units.smul_def]
  change ((-1 : ℤ) ^ p • (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap (𝟙 _) (integerChainInterval.d (q + 1) q) ≫ _)) ≫ _ = _
  rw [Preadditive.zsmul_comp, Category.assoc, ι_chainHomotopyIntervalApp]

/-- 概要：区間が零次なら垂直微分の後の評価は零。
方針：零次からの垂直微分がないことを使う。
規約：KST A.3・A.5。使われ方：頂点の評価の微分条件。 -/
lemma chainInterval_ι_D₂_zero {p n s : ℕ} (h : p + 0 = s) :
    ιMapBifunctor K integerChainInterval _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor (.down ℕ) p 0 s h ≫
      mapBifunctor.D₂ K integerChainInterval _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor (.down ℕ) s n ≫
      chainHomotopyIntervalApp H n = 0 := by
  rw [← Category.assoc, mapBifunctor.ι_D₂,
    mapBifunctor.d₂_eq_zero _ _ _ _ p 0 n (by simp), Limits.zero_comp]

end SerrePositivity.KST.ProExcision
