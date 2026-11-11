module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.EZHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NormalizedShuffle
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ChainTensorHomotopy

/-!
# 正規化した AW→shuffle の恒等との比較

概要：Moore 複体上でも正規化 AW→shuffle と恒等の間の実鎖ホモトピーを構成する。
方針：普遍模型の比較を包含・射影で挟み、両因子の Moore 収縮をテンソルして合成する。
規約：KST Construction A.5、非被約 C(H) を保ち追加の比較仮定を置かない。
使われ方：正規化した二つの差のテンソルの低次消滅を対角へ移す。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory HomologicalComplex AlgebraicTopology AlgebraicTopology.DoldKan
variable (C D : SimplicialObject (ModuleCat.{u} ℤ))

/-- 概要：恒等から正規化前の比較を Moore 包含・射影で挟んだ写像へのホモトピー。
方針：実 EZ ホモトピーを左右から合成し、Moore 分裂を使う。
規約：KST A.5、対角だけを正規化した段階。
使われ方：両因子の正規化を挟む前の比較。 -/
def normalizedEZRawHomotopy : Homotopy (𝟙 _)
    (inclusionOfMooreComplexMap (simplicialIntegerTensor C D) ≫
      alexanderWhitney C D ≫ shuffle C D ≫
      PInftyToNormalizedMooreComplex (simplicialIntegerTensor C D)) := by
  let h := ((ezHomotopy C D).compLeft
    (inclusionOfMooreComplexMap (simplicialIntegerTensor C D))).compRight
      (PInftyToNormalizedMooreComplex (simplicialIntegerTensor C D))
  refine (Homotopy.ofEq ?_).trans (h.trans (Homotopy.ofEq ?_))
  · have hi : inclusionOfMooreComplexMap (simplicialIntegerTensor C D) ≫
        PInftyToNormalizedMooreComplex (simplicialIntegerTensor C D) = 𝟙 _ :=
        (splitMonoInclusionOfMooreComplexMap (simplicialIntegerTensor C D)).id
    simpa only [Category.comp_id] using hi.symm
  · simp only [Category.assoc]

/-- 概要：両因子の正規化を挟む前の比較から正規化 AW→shuffle へのホモトピー。
方針：Moore 射影・包含の全テンソルと恒等のホモトピーを左右から合成する。
規約：KST A.5、全テンソルの実鎖ホモトピーを使う。
使われ方：標準比較を正規化した両因子のテンソルへ移す。 -/
def normalizedEZInsertMooreHomotopy : Homotopy
    (inclusionOfMooreComplexMap (simplicialIntegerTensor C D) ≫
      alexanderWhitney C D ≫ shuffle C D ≫
      PInftyToNormalizedMooreComplex (simplicialIntegerTensor C D))
    (normalizedAlexanderWhitney C D ≫ normalizedShuffle C D) := by
  let h := ((chainIntegerTensorMooreRetraction C D).symm.compLeft
    (inclusionOfMooreComplexMap (simplicialIntegerTensor C D) ≫ alexanderWhitney C D)).compRight
      (shuffle C D ≫ PInftyToNormalizedMooreComplex (simplicialIntegerTensor C D))
  refine (Homotopy.ofEq ?_).trans (h.trans (Homotopy.ofEq ?_))
  · change _ = ((inclusionOfMooreComplexMap (simplicialIntegerTensor C D) ≫
        alexanderWhitney C D) ≫ 𝟙 _) ≫
        (shuffle C D ≫ PInftyToNormalizedMooreComplex (simplicialIntegerTensor C D))
    rw [Category.comp_id, Category.assoc]
  · dsimp only [normalizedAlexanderWhitney, normalizedShuffle]
    rw [chainIntegerTensorMap_comp]
    simp only [Category.assoc]

/-- 概要：正規化 Moore 複体の恒等と正規化 AW→shuffle の実鎖ホモトピー。
方針：普遍模型による比較と両因子の Moore 収縮のテンソルを合成する。
規約：KST Construction A.5、標準比較の存在を仮定しない。
使われ方：低次の補正式を正規化した対角の比較へ送る。 -/
def normalizedEZHomotopy : Homotopy (𝟙 _)
    (normalizedAlexanderWhitney C D ≫ normalizedShuffle C D) :=
  (normalizedEZRawHomotopy C D).trans (normalizedEZInsertMooreHomotopy C D)

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
