module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleBoundaryDecomposition
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWTensorDifferential
public import Mathlib.Tactic.CrossRefAttribute

/-!
# 標準 shuffle の実鎖写像

概要：格子路の有限和は全テンソルと対角の交代面微分に可換。
方針：全複体の標準包含ごとに水平・垂直微分を評価し、混合境界の消滅を使う。
規約：KST Construction A.5 の標準 shuffle、非被約な零次を含む。
使われ方：AW との標準比較と正規化複体への移送。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory Opposite HomologicalComplex AlgebraicTopology
open scoped Simplicial
variable (C D : SimplicialObject (ModuleCat.{u} ℤ))

/-- 概要：全テンソルの水平微分の後の shuffle は純粋水平境界和。
方針：第一因子の零次を分け、正の次数で交代面微分を展開する。
規約：KST A.5。使われ方：shuffle の鎖写像性の水平部分。 -/
lemma shuffle_horizontal_differential {p q n : ℕ} (h : p + q = n + 1) :
    ιMapBifunctor ((alternatingFaceMapComplex _).obj C)
      ((alternatingFaceMapComplex _).obj D) integerTensorBifunctor (.down ℕ) p q (n + 1) h ≫
      mapBifunctor.D₁ ((alternatingFaceMapComplex _).obj C)
        ((alternatingFaceMapComplex _).obj D) integerTensorBifunctor (.down ℕ) (n + 1) n ≫
      shuffleApp C D n =
    ∑ z : AllHorizontalShuffleBoundaryIndex p n, shuffleBoundaryWeight C D h z.val := by
  rw [← Category.assoc, mapBifunctor.ι_D₁]
  cases p with
  | zero =>
    rw [mapBifunctor.d₁_eq_zero _ _ _ _ 0 q n (by simp), Limits.zero_comp,
      shuffleBoundary_horizontal_zero C D h]
  | succ p =>
    have h' : p + q = n := by omega
    rw [mapBifunctor.d₁_eq _ _ _ _ (i₁ := p + 1) (i₁' := p) rfl q n h']
    have hε : ComplexShape.ε₁ (.down ℕ) (.down ℕ) (.down ℕ) (p + 1, q) = 1 := rfl
    rw [hε, one_smul]
    change (integerTensorMap (((alternatingFaceMapComplex _).obj C).d (p + 1) p)
      (𝟙 _) ≫ _) ≫ _ = _
    rw [Category.assoc, ι_shuffleApp, shuffleBoundary_horizontal_succ C D h',
      alternatingFaceMapComplex_obj_d, AlternatingFaceMapComplex.objD,
      integerTensorMap_sum_left, Preadditive.sum_comp]
    apply Finset.sum_congr rfl
    intro i _
    rw [integerTensorMap_zsmul_left, Preadditive.zsmul_comp]
    rfl

/-- 概要：全テンソルの垂直微分の後の shuffle は純粋垂直境界和。
方針：第二因子の零次を分け、全複体の符号を保って交代面微分を展開する。
規約：KST A.5、垂直符号は (−1)^p。
使われ方：shuffle の鎖写像性の垂直部分。 -/
lemma shuffle_vertical_differential {p q n : ℕ} (h : p + q = n + 1) :
    ιMapBifunctor ((alternatingFaceMapComplex _).obj C)
      ((alternatingFaceMapComplex _).obj D) integerTensorBifunctor (.down ℕ) p q (n + 1) h ≫
      mapBifunctor.D₂ ((alternatingFaceMapComplex _).obj C)
        ((alternatingFaceMapComplex _).obj D) integerTensorBifunctor (.down ℕ) (n + 1) n ≫
      shuffleApp C D n =
    ∑ z : AllVerticalShuffleBoundaryIndex p n, shuffleBoundaryWeight C D h z.val := by
  rw [← Category.assoc, mapBifunctor.ι_D₂]
  cases q with
  | zero =>
    rw [mapBifunctor.d₂_eq_zero _ _ _ _ p 0 n (by simp), Limits.zero_comp,
      shuffleBoundary_vertical_zero C D h]
  | succ q =>
    have h' : p + q = n := by omega
    rw [mapBifunctor.d₂_eq _ _ _ _ p (i₂ := q + 1) (i₂' := q) rfl n h']
    have hε : ComplexShape.ε₂ (.down ℕ) (.down ℕ) (.down ℕ) (p, q + 1) =
      (-1 : ℤˣ) ^ p := rfl
    rw [hε, Units.smul_def]
    change ((-1 : ℤ) ^ p • (integerTensorMap (𝟙 _)
      (((alternatingFaceMapComplex _).obj D).d (q + 1) q) ≫ _)) ≫ _ = _
    rw [Preadditive.zsmul_comp, Category.assoc, ι_shuffleApp,
      shuffleBoundary_vertical_succ C D h']
    congr 1
    rw [alternatingFaceMapComplex_obj_d, AlternatingFaceMapComplex.objD,
      integerTensorMap_sum_right, Preadditive.sum_comp]
    apply Finset.sum_congr rfl
    intro i _
    rw [integerTensorMap_zsmul_right, Preadditive.zsmul_comp]
    rfl

/-- 概要：shuffle の成分は全テンソルの微分と対角の微分に可換。
方針：標準直和包含で比較し、二種類の純粋境界和を合成する。
規約：KST Construction A.5、実際の鎖複体に対する等式。
使われ方：標準 shuffle の鎖写像の構成。 -/
@[kerodon 00RN]
theorem shuffle_comm (n : ℕ) :
    shuffleApp C D (n + 1) ≫
      ((alternatingFaceMapComplex _).obj (simplicialIntegerTensor C D)).d (n + 1) n =
    (chainIntegerTensor ((alternatingFaceMapComplex _).obj C)
      ((alternatingFaceMapComplex _).obj D)).d (n + 1) n ≫ shuffleApp C D n := by
  apply mapBifunctor.hom_ext
  intro p q h
  rw [← Category.assoc, ι_shuffleApp, shuffleBidegree_boundary_pure,
    mapBifunctor.d_eq, Preadditive.add_comp, Preadditive.comp_add]
  rw [shuffle_horizontal_differential C D h, shuffle_vertical_differential C D h]

/-- 概要：標準 shuffle の実鎖写像。
方針：格子路の符号付き有限和に検証済みの微分との可換性を付ける。
規約：KST Construction A.5、正規化前の交代面複体。
使われ方：Moore 複体への移送と AW との標準ホモトピー。 -/
@[kerodon 00RN]
def shuffle :
    chainIntegerTensor ((alternatingFaceMapComplex _).obj C)
      ((alternatingFaceMapComplex _).obj D) ⟶
    (alternatingFaceMapComplex _).obj (simplicialIntegerTensor C D) :=
  ChainComplex.ofHom (shuffleApp C D) (shuffle_comm C D)

/-- 概要：標準 shuffle は二つの単体的整数加群の射に自然。
方針：成分の自然性を鎖写像の等式として束ねる。
規約：KST A.5、外部群の作用も含む。
使われ方：比較の同変性と正規化。 -/
lemma shuffle_naturality
    {C C' D D' : SimplicialObject (ModuleCat.{u} ℤ)} (f : C ⟶ C') (g : D ⟶ D') :
    chainIntegerTensorMap ((alternatingFaceMapComplex _).map f)
        ((alternatingFaceMapComplex _).map g) ≫ shuffle C' D' =
      shuffle C D ≫ (alternatingFaceMapComplex _).map (simplicialIntegerTensorMap f g) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact shuffleApp_naturality f g n

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
