module
public import SerrePositivity.KST.ProExcision.ChainIntervalEvaluationChainMap
public import SerrePositivity.KST.ProExcision.IntegerIntervalComparison
public import SerrePositivity.KST.ProExcision.NormalizedMapReconstruction
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NormalizedEZHomotopy

/-!
# 鎖ホモトピーから単体的テンソル区間射への復元

概要：実 AW と鎖区間の比較を通し、Dold–Kan の充満性で単体的な区間射を構成する。
方針：Moore 包含、AW、第一因子の射影・区間の比較、ホモトピーの評価を合成する。
規約：KST Definition A.3、Construction A.5、非被約 C(H) を保つ。両端条件は別途証明する。
使われ方：正規化した augmentation 補正式の鎖比較を実区間ホモトピーへ移す。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite HomologicalComplex AlgebraicTopology AlgebraicTopology.DoldKan
open scoped Simplicial
variable {C D : SimplicialObject (ModuleCat.{u} ℤ)} {f g : C ⟶ D}

/-- 概要：正規化前の単体的テンソル区間からの実鎖写像。
方針：AW、第一因子の Moore 射影、区間の比較、ホモトピー評価を合成する。
規約：KST A.3・A.5。使われ方：自由基底で区間の両端を計算する。 -/
def chainHomotopyCylinderCore
    (H : Homotopy ((normalizedMooreComplex _).map f) ((normalizedMooreComplex _).map g)) :
    (alternatingFaceMapComplex _).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensor C (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u}))) ⟶
      (normalizedMooreComplex _).obj D :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitney C (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u})) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap (PInftyToNormalizedMooreComplex C) integerIntervalComparison ≫
      chainHomotopyInterval H

/-- 概要：鎖ホモトピーから正規化した単体的テンソル区間の実鎖写像を作る。
方針：AW と単体的区間の実鎖比較を通して構成済みのホモトピー評価へ送る。
規約：KST A.3・A.5、全ての比較は実鎖写像。
使われ方：Dold–Kan による実区間射への復元の入力。 -/
def chainHomotopyCylinderMap
    (H : Homotopy ((normalizedMooreComplex _).map f) ((normalizedMooreComplex _).map g)) :
    (normalizedMooreComplex _).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensor C (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u}))) ⟶
      (normalizedMooreComplex _).obj D :=
  inclusionOfMooreComplexMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensor C (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u}))) ≫
    chainHomotopyCylinderCore H

/-- 概要：正規化鎖ホモトピーを単体的テンソル区間からの実射へ復元する。
方針：構成済みの実鎖写像に Dold–Kan の前像を適用する。
規約：KST A.3・A.5、単体的射の構成であり両端条件は別工程。
使われ方：非被約 C(H) の実区間ホモトピーの構成。 -/
def chainHomotopyCylinderReconstruct
    (H : Homotopy ((normalizedMooreComplex _).map f) ((normalizedMooreComplex _).map g)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensor C (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u})) ⟶ D :=
  normalizedMapReconstruct (chainHomotopyCylinderMap H)

/-- 概要：復元した実単体的区間射の正規化は構成した区間の鎖写像に一致。
方針：Dold–Kan の復元の評価公式を使う。
規約：KST A.3・A.5。使われ方：両端と同変性の検証を鎖計算へ移す。 -/
lemma chainHomotopyCylinderReconstruct_map
    (H : Homotopy ((normalizedMooreComplex _).map f) ((normalizedMooreComplex _).map g)) :
    (normalizedMooreComplex _).map (chainHomotopyCylinderReconstruct H) =
      chainHomotopyCylinderMap H :=
  normalizedMapReconstruct_map _

end SerrePositivity.KST.ProExcision
