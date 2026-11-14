module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWChainMap
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NormalizedStrictification

/-!
# 正規化 Moore 複体の Alexander–Whitney 写像

概要：標準 AW の実鎖写像を正規化 Moore 複体の包含と射影で移送する。
方針：始域を正規化したテンソルから包含し、終域の両因子を PInfty で射影する。
規約：KST Construction A.5、非被約な複体を保つ。任意の加群の宇宙で構成する。
使われ方：二つの差の正規化全テンソルの消滅を使う比較。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory Opposite HomologicalComplex AlgebraicTopology AlgebraicTopology.DoldKan
open scoped Simplicial

/-- 概要：二つの鎖写像の全テンソルは合成を保つ。
方針：全次数の標準包含とテンソル写像の合成則で検出する。
規約：KST A.5、ℕ 次数の全複体。使われ方：正規化した比較の自然性。 -/
lemma chainIntegerTensorMap_comp
    {K K' K'' L L' L'' : ChainComplex (ModuleCat.{u} ℤ) ℕ}
    (f : K ⟶ K') (f' : K' ⟶ K'') (g : L ⟶ L') (g' : L' ⟶ L'') :
    chainIntegerTensorMap (f ≫ f') (g ≫ g') =
      chainIntegerTensorMap f g ≫ chainIntegerTensorMap f' g' := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply mapBifunctor.hom_ext
  intro i j h
  rw [comp_f, ι_chainIntegerTensorMap]
  rw [← Category.assoc (ιMapBifunctor K L integerTensorBifunctor (.down ℕ) i j n h)]
  rw [ι_chainIntegerTensorMap, Category.assoc, ι_chainIntegerTensorMap]
  rw [← Category.assoc, ← integerTensorMap_comp]
  rfl

/-- 概要：正規化 Moore 複体から正規化した両因子の全テンソルへの AW 鎖写像。
方針：包含、標準 AW、二つの PInfty 射影の全テンソルを合成する。
規約：KST Construction A.5、Mathlib の Moore 複体の模型。
使われ方：正規化した差の低次数消滅を挟む比較の前半。 -/
def normalizedAlexanderWhitney (C D : SimplicialObject (ModuleCat.{u} ℤ)) :
    (normalizedMooreComplex _).obj (simplicialIntegerTensor C D) ⟶
      chainIntegerTensor ((normalizedMooreComplex _).obj C) ((normalizedMooreComplex _).obj D) :=
  inclusionOfMooreComplexMap (simplicialIntegerTensor C D) ≫ alexanderWhitney C D ≫
    chainIntegerTensorMap (PInftyToNormalizedMooreComplex C) (PInftyToNormalizedMooreComplex D)

/-- 概要：正規化 AW は二つの単体的整数加群の射に自然。
方針：包含の自然性、標準 AW の自然性、PInfty 射影の自然性を合成する。
規約：KST A.5、因子の群の可換性に依存しない。
使われ方：μ へ移す前の比較の外部 G 同変性。 -/
lemma normalizedAlexanderWhitney_naturality
    {C C' D D' : SimplicialObject (ModuleCat.{u} ℤ)} (f : C ⟶ C') (g : D ⟶ D') :
    (normalizedMooreComplex _).map (simplicialIntegerTensorMap f g) ≫
        normalizedAlexanderWhitney C' D' =
      normalizedAlexanderWhitney C D ≫
        chainIntegerTensorMap ((normalizedMooreComplex _).map f)
          ((normalizedMooreComplex _).map g) := by
  have hi := (inclusionOfMooreComplex (ModuleCat.{u} ℤ)).naturality (simplicialIntegerTensorMap f g)
  have hp := PInftyToNormalizedMooreComplex_naturality f
  have hq := PInftyToNormalizedMooreComplex_naturality g
  change (normalizedMooreComplex _).map (simplicialIntegerTensorMap f g) ≫
      inclusionOfMooreComplexMap (simplicialIntegerTensor C' D') =
    inclusionOfMooreComplexMap (simplicialIntegerTensor C D) ≫
      (alternatingFaceMapComplex _).map (simplicialIntegerTensorMap f g) at hi
  change (alternatingFaceMapComplex _).map f ≫ PInftyToNormalizedMooreComplex C' =
    PInftyToNormalizedMooreComplex C ≫ (normalizedMooreComplex _).map f at hp
  change (alternatingFaceMapComplex _).map g ≫ PInftyToNormalizedMooreComplex D' =
    PInftyToNormalizedMooreComplex D ≫ (normalizedMooreComplex _).map g at hq
  dsimp only [normalizedAlexanderWhitney]
  rw [← Category.assoc, hi]
  simp only [Category.assoc]
  rw [← Category.assoc ((alternatingFaceMapComplex _).map (simplicialIntegerTensorMap f g)),
    alexanderWhitney_naturality]
  simp only [Category.assoc]
  rw [← chainIntegerTensorMap_comp, hp, hq, chainIntegerTensorMap_comp]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.2.3.24" (partial := special) "仮定：整数加群の単体的対象二つとそれぞれの射（Lean が強い：二変数テンソルに特化）。結論：正規化・非正規化の Alexander–Whitney 写像が各射について可換（二変数の場合は一致）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedAlexanderWhitney_naturality
attribute [cite HA "1.2.3.26" (partial := component) "仮定：整数加群のテンソル（Lean が強い：一般の冪等完備な加法的モノイダル圏ではない）。結論：正規化と非正規化それぞれのテンソル比較射。一般の両関手の oplax monoidal 構造を返す型は含まれない（Lean が弱い）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedAlexanderWhitney
