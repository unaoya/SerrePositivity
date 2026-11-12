module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.IntegerTensorBifunctor
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NormalizedStrictification
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Tactic.Abel
public import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# ℕ 次数の正規化テンソルの低次数消滅

概要：二つの鎖写像がそれぞれ次数 ≤m、≤m′ で零なら、全テンソルは次数 ≤m+m′+1 で零。
方針：通常の全複体の各直和成分 i+j=n について、少なくとも片方の写像が零であることを使う。
規約：KST Construction A.5、非被約複体の差に適用する。スペクトル系列を使わない。
使われ方：正規化した二つの差のテンソルの消滅と augmentation 補正式。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory HomologicalComplex
variable {K K' L L' : ChainComplex (ModuleCat.{u} ℤ) ℕ}

/-- 概要：整数加群の全テンソルに必要な直和は存在する。
方針：各全次数で ModuleCat の余積を使う。
規約：KST A.5、通常の全複体。使われ方：ℕ 次数のテンソルの存在。 -/
instance chainIntegerTensor_hasTotal (K L : ChainComplex (ModuleCat.{u} ℤ) ℕ) :
    HasMapBifunctor K L integerTensorBifunctor (.down ℕ) := by
  intro n
  infer_instance

/-- 概要：ℕ 次数の整数加群の鎖複体の全テンソル。
方針：明示的な整数テンソル双関手の全複体を使う。
規約：KST A.5、任意の加群の宇宙。使われ方：正規化した複体のテンソル。 -/
abbrev chainIntegerTensor (K L : ChainComplex (ModuleCat.{u} ℤ) ℕ) :
    ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  mapBifunctor K L integerTensorBifunctor (.down ℕ)

/-- 概要：二つの鎖写像の全テンソル。
方針：各二重次数のテンソル写像から誘導する。
規約：KST A.5、i+j=n の全複体。使われ方：差のテンソルと補正和の比較。 -/
abbrev chainIntegerTensorMap (f : K ⟶ K') (g : L ⟶ L') :
    chainIntegerTensor K L ⟶ chainIntegerTensor K' L' :=
  mapBifunctorMap f g integerTensorBifunctor (.down ℕ)

/-- 概要：二つの差のテンソルの低次数消滅。
方針：i+j=n の各成分で i≤m または j≤m′ を使う。
規約：KST A.5、次数の上限 m+m′+1 は零次を含む。
使われ方：正規化した入力から AW/shuffle の比較の中央の等式を得る。 -/
lemma chainIntegerTensorMap_eq_zero_low (f : K ⟶ K') (g : L ⟶ L') (m m' : ℕ)
    (hf : ∀ i, i ≤ m → f.f i = 0) (hg : ∀ j, j ≤ m' → g.f j = 0)
    (n : ℕ) (hn : n ≤ m + m' + 1) : (chainIntegerTensorMap f g).f n = 0 := by
  apply mapBifunctor.hom_ext
  intro i j hij
  rw [ι_mapBifunctorMap]
  have hsum : i + j = n := hij
  by_cases hi : i ≤ m
  · rw [hf i hi]
    simp
  · have hj : j ≤ m' := by omega
    rw [hg j hj]
    simp

/-- 概要：全テンソル写像の第一変数の引き算は通常の差に一致する。
方針：各直和成分で双関手の加法性を使う。
規約：KST A.5。使われ方：差のテンソルの augmentation 展開。 -/
lemma chainIntegerTensorMap_sub_left (f e : K ⟶ K') (g : L ⟶ L') :
    chainIntegerTensorMap (f - e) g = chainIntegerTensorMap f g - chainIntegerTensorMap e g := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply mapBifunctor.hom_ext
  intro i j hij
  simp only [chainIntegerTensorMap, sub_f_apply, Preadditive.comp_sub,
    ι_mapBifunctorMap, CategoryTheory.Functor.map_sub, NatTrans.app_sub,
    Preadditive.sub_comp]

/-- 概要：全テンソル写像の第二変数の引き算は通常の差に一致する。
方針：各直和成分で第二変数の加法性を使う。
規約：KST A.5。使われ方：差のテンソルの augmentation 展開。 -/
lemma chainIntegerTensorMap_sub_right (f : K ⟶ K') (g e : L ⟶ L') :
    chainIntegerTensorMap f (g - e) = chainIntegerTensorMap f g - chainIntegerTensorMap f e := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply mapBifunctor.hom_ext
  intro i j hij
  simp only [chainIntegerTensorMap, sub_f_apply, Preadditive.comp_sub,
    ι_mapBifunctorMap, CategoryTheory.Functor.map_sub, Preadditive.sub_comp]

/-- 概要：二つの差の全テンソルは augmentation 補正の四項の差。
方針：両変数の引き算を展開する。
規約：KST A.5 の右辺の augmentation 補正。
使われ方：低次数の消滅を補正和の一致へ変える。 -/
lemma chainIntegerTensorMap_augmentation_expansion (f e : K ⟶ K') (g e' : L ⟶ L') :
    chainIntegerTensorMap (f - e) (g - e') =
      chainIntegerTensorMap f g - chainIntegerTensorMap f e' -
        chainIntegerTensorMap e g + chainIntegerTensorMap e e' := by
  rw [chainIntegerTensorMap_sub_left, chainIntegerTensorMap_sub_right,
    chainIntegerTensorMap_sub_right]
  abel

/-- 概要：全テンソルの補正和は次数 ≤m+m′+1 で元のテンソルに一致する。
方針：二つの差の低次数消滅と双線形展開を合成する。
規約：KST A.5 の右辺の augmentation 補正、零次を含む。
使われ方：AW/shuffle の比較の中央の等式。 -/
lemma chainIntegerTensorMap_augmentation_eq_low (f e : K ⟶ K') (g e' : L ⟶ L')
    (m m' : ℕ) (hf : ∀ i, i ≤ m → f.f i = e.f i)
    (hg : ∀ j, j ≤ m' → g.f j = e'.f j) (n : ℕ) (hn : n ≤ m + m' + 1) :
    (chainIntegerTensorMap f g).f n =
      (chainIntegerTensorMap f e' + chainIntegerTensorMap e g - chainIntegerTensorMap e e').f n := by
  have hz := chainIntegerTensorMap_eq_zero_low (f - e) (g - e') m m'
    (fun i hi ↦ by rw [sub_f_apply, hf i hi, sub_self])
    (fun j hj ↦ by rw [sub_f_apply, hg j hj, sub_self]) n hn
  rw [chainIntegerTensorMap_augmentation_expansion] at hz
  simp only [add_f_apply, sub_f_apply] at hz ⊢
  apply sub_eq_zero.mp
  convert hz using 1
  abel

/-- 概要：二つの因子内の入力ホモトピーを厳密化・正規化したテンソルの補正式。
方針：正規化後の低次数一致を全テンソルの次数評価へ渡す。
規約：KST A.5 の右辺の augmentation 補正。m+m′+1 の範囲での実鎖写像の等式。
使われ方：AW と shuffle の間に挟む等式。比較ホモトピー自体は別途構成する。 -/
lemma normalizedStrictifiedTensor_eq_low
    {X Y : SSet.{u}} {D E : SimplicialObject (ModuleCat.{u} ℤ)}
    {f e : linearizedSpace X ⟶ D} {g e' : linearizedSpace Y ⟶ E} {m m' : ℕ}
    (h : LinearizedMHomotopy f e m) (h' : LinearizedMHomotopy g e' m')
    (n : ℕ) (hn : n ≤ m + m' + 1) :
    (chainIntegerTensorMap ((AlgebraicTopology.normalizedMooreComplex _).map h.strictifiedMap)
      ((AlgebraicTopology.normalizedMooreComplex _).map h'.strictifiedMap)).f n =
    (chainIntegerTensorMap ((AlgebraicTopology.normalizedMooreComplex _).map h.strictifiedMap)
        ((AlgebraicTopology.normalizedMooreComplex _).map e') +
      chainIntegerTensorMap ((AlgebraicTopology.normalizedMooreComplex _).map e)
        ((AlgebraicTopology.normalizedMooreComplex _).map h'.strictifiedMap) -
      chainIntegerTensorMap ((AlgebraicTopology.normalizedMooreComplex _).map e)
        ((AlgebraicTopology.normalizedMooreComplex _).map e')).f n :=
  chainIntegerTensorMap_augmentation_eq_low _ _ _ _ m m'
    h.normalized_strictifiedMap_eq_low h'.normalized_strictifiedMap_eq_low n hn

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories


