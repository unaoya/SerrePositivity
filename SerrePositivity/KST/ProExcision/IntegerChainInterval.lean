module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.IntegerLinearizationDesc
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ChainTensorVanishing
public import Mathlib.Algebra.Module.PUnit

/-!
# 整数鎖複体の標準区間

概要：二つの頂点と一つの辺を持つ非被約な二項鎖複体を作る。
方針：辺の境界を終点から始点を引いたものとして定める。
規約：KST Definition A.3、Construction A.5 の単体的区間への復元に使う。
使われ方：鎖ホモトピーから実際のテンソル区間写像を構成する中間模型。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory

/-- 概要：標準鎖区間の次数ごとの整数加群。
方針：零次は二つの頂点、一次は一つの辺、二次以降は零対象。
規約：KST A.3・A.5、増大を持つ非被約模型。
使われ方：鎖ホモトピーの区間への評価。 -/
def integerIntervalX : ℕ → ModuleCat.{u} ℤ
  | 0 => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.obj (ULift.{u} (Fin 2))
  | 1 => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.obj (ULift.{u} PUnit)
  | _ + 2 => ModuleCat.of ℤ PUnit.{u + 1}

/-- 概要：標準鎖区間の二つの頂点の基底。
方針：零次自由整数加群の単項基底。
規約：KST A.3、頂点0が始点、頂点1が終点。
使われ方：区間写像の両端。 -/
def integerIntervalVertex (i : Fin 2) : integerIntervalX.{u} 0 :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (ULift.up i)

/-- 概要：標準鎖区間の辺の基底。
方針：一次自由整数加群の唯一の基底。
規約：KST A.3。使われ方：鎖ホモトピーの一段上の成分の評価。 -/
def integerIntervalEdge : integerIntervalX.{u} 1 :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (ULift.up PUnit.unit)

/-- 概要：辺の境界は終点から始点を引いたもの。
方針：唯一の辺の基底上の値を整数線形に拡張する。
規約：KST A.3・A.5、標準の区間の向き。
使われ方：鎖ホモトピー等式と区間の鎖写像性の接続。 -/
def integerIntervalBoundary : integerIntervalX.{u} 1 ⟶ integerIntervalX.{u} 0 :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearizationDesc (fun _ ↦ integerIntervalVertex 1 - integerIntervalVertex 0)

/-- 概要：区間の辺の境界の実計算。
方針：整数線形拡張を唯一の基底へ評価する。
規約：KST A.3。使われ方：両端の差のホモトピー条件。 -/
lemma integerIntervalBoundary_edge :
    integerIntervalBoundary.{u} integerIntervalEdge = integerIntervalVertex 1 - integerIntervalVertex 0 :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearizationDesc_generator _ _

/-- 概要：鎖区間の隣接次数の微分。
方針：一次から零次だけ辺の境界を使い、他の微分は零。
規約：KST A.3・A.5。使われ方：実鎖複体の構成。 -/
def integerIntervalD : (n : ℕ) → integerIntervalX.{u} (n + 1) ⟶ integerIntervalX n
  | 0 => integerIntervalBoundary
  | _ + 1 => 0

/-- 概要：標準整数区間の実鎖複体。
方針：辺の境界だけを持つ二項複体とする。
規約：KST A.3・A.5、非被約零次を保つ。
使われ方：単体的テンソル区間から鎖ホモトピーへの接続。 -/
def integerChainInterval : ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  ChainComplex.of integerIntervalX integerIntervalD (fun n ↦ by
    cases n <;> simp only [integerIntervalD, Limits.zero_comp])

end SerrePositivity.KST.ProExcision
