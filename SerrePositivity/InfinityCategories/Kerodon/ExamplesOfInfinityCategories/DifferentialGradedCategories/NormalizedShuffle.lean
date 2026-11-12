module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleChainMap
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NormalizedAlexanderWhitney
public import Mathlib.Tactic.CrossRefAttribute

/-!
# 正規化 Moore 複体の shuffle 写像

概要：標準 shuffle を両因子の Moore 包含と対角の射影で正規化する。
方針：実鎖写像の合成として定義し、三つの比較写像の自然性を使う。
規約：KST Construction A.5、非被約 C(H) の零次を保つ。
使われ方：差の全テンソルの低次消滅を対角へ戻す比較。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory Opposite HomologicalComplex AlgebraicTopology AlgebraicTopology.DoldKan
open scoped Simplicial

/-- 概要：正規化した両因子の全テンソルから対角の Moore 複体への shuffle。
方針：二つの Moore 包含のテンソル、実 shuffle、対角の PInfty 射影を合成する。
規約：KST Construction A.5、零次 augmentation を落とさない。
使われ方：正規化した差のテンソルを挟む比較の後半。 -/
@[kerodon 00RS]
def normalizedShuffle (C D : SimplicialObject (ModuleCat.{u} ℤ)) :
    chainIntegerTensor ((normalizedMooreComplex _).obj C) ((normalizedMooreComplex _).obj D) ⟶
      (normalizedMooreComplex _).obj (simplicialIntegerTensor C D) :=
  chainIntegerTensorMap (inclusionOfMooreComplexMap C) (inclusionOfMooreComplexMap D) ≫
    shuffle C D ≫ PInftyToNormalizedMooreComplex (simplicialIntegerTensor C D)

/-- 概要：正規化 shuffle は二つの単体的整数加群の射に自然。
方針：包含、shuffle、Moore 射影の自然性を順に合成する。
規約：KST A.5、外部群の作用の写像も含む。
使われ方：μ の適用前の比較の同変性。 -/
lemma normalizedShuffle_naturality
    {C C' D D' : SimplicialObject (ModuleCat.{u} ℤ)} (f : C ⟶ C') (g : D ⟶ D') :
    chainIntegerTensorMap ((normalizedMooreComplex _).map f)
        ((normalizedMooreComplex _).map g) ≫ normalizedShuffle C' D' =
      normalizedShuffle C D ≫
        (normalizedMooreComplex _).map (simplicialIntegerTensorMap f g) := by
  have hi := (inclusionOfMooreComplex (ModuleCat.{u} ℤ)).naturality f
  have hj := (inclusionOfMooreComplex (ModuleCat.{u} ℤ)).naturality g
  change (normalizedMooreComplex _).map f ≫ inclusionOfMooreComplexMap C' =
    inclusionOfMooreComplexMap C ≫ (alternatingFaceMapComplex _).map f at hi
  change (normalizedMooreComplex _).map g ≫ inclusionOfMooreComplexMap D' =
    inclusionOfMooreComplexMap D ≫ (alternatingFaceMapComplex _).map g at hj
  have hp := PInftyToNormalizedMooreComplex_naturality (simplicialIntegerTensorMap f g)
  change (alternatingFaceMapComplex _).map (simplicialIntegerTensorMap f g) ≫
      PInftyToNormalizedMooreComplex (simplicialIntegerTensor C' D') =
    PInftyToNormalizedMooreComplex (simplicialIntegerTensor C D) ≫
      (normalizedMooreComplex _).map (simplicialIntegerTensorMap f g) at hp
  dsimp only [normalizedShuffle]
  rw [← Category.assoc, ← chainIntegerTensorMap_comp, hi, hj, chainIntegerTensorMap_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (chainIntegerTensorMap ((alternatingFaceMapComplex _).map f)
    ((alternatingFaceMapComplex _).map g)), shuffle_naturality]
  simp only [Category.assoc]
  rw [hp]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
