module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePullbackPathLifting
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.EquivalenceLiftingInvertible
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativePathBoundary
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：同値を右に持ち上げる射に沿って、同じ同値写像を厳密に引き戻す。
方針：可逆辺の終点指定の持ち上げから相対 path の全境界持ち上げを得る。
規約：モデル構造の instance を仮定しない。
使われ方：実際の分類先の Hom の成分比較を同じ底へ引き戻す。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 同値を右に持ち上げる射に沿う、元の同値の厳密な引き戻しは同値。 -/
@[kerodon 01HJ]
lemma IsQCatEquivalence.pullback_snd_isPrecompositionEquivalence_of_kanEquivalenceLifting
    {E B F : SSet.{u}} [Quasicategory E] [Quasicategory B] [Quasicategory F]
    {e : E ⟶ B} (he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence e) (p : F ⟶ B)
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (pullback.snd e p) := by
  letI : InnerFibration p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting.innerFibration hp
  letI : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt p 1) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeEquivalencePathMapAt_one_trivialKanFibration p
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.EquivalenceLifting.invertibleTargetLifting hp)
  exact (he.pullback_snd_of_relativePath p).isPrecompositionEquivalence

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsQCatEquivalence (pullback_snd_isPrecompositionEquivalence_of_kanEquivalenceLifting)


end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "B.3.15" (partial := stronger-hyp) "仮定：A,B,Cは準圏、A→Bは圏同値、p:C→Bは全単射な前合成同値を持ち上げるEquivalenceLiftingを満たす（Leanが強い：A,Bの準圏性と操作的RLPを明記）。結論：同じpullback射A×B C→Cは前合成同値、従って圏同値（指定された引き戻し比較の結論に一致）。任意simplicial set A,Bおよびflat categorical fibrationの定義だけからの全比較は含まれない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsQCatEquivalence.pullback_snd_isPrecompositionEquivalence_of_kanEquivalenceLifting
attribute [cite HTT "2.4.4.5" (partial := stronger-hyp) "仮定：C,D,D′ は準圏、Cartesian p にさらに EquivalenceLifting p を明示して追加（Lean が強い）。結論：同じ pullback projection q′ は IsPrecompositionEquivalence、pullback の準圏性の下で IsQCatEquivalence に一致する。Cartesian 性から追加 lifting を導く比較は含めず、追加仮定の下だけを数える。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsQCatEquivalence.pullback_snd_isPrecompositionEquivalence_of_kanEquivalenceLifting
attribute [cite HTT "2.4.7.7" (partial := stronger-hyp) "仮定：元の bifibration p に EquivalenceLifting p、全空間の準圏性、積の base-change map の native QCatEquivalence を追加（Lean が強い）。結論：同じ X′→X は IsPrecompositionEquivalence となり、引戻しを含む両側の準圏性から IsQCatEquivalence を得る。bifibration と f,g の仮定だけからこれらの追加条件を導く部分は含まない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsQCatEquivalence.pullback_snd_isPrecompositionEquivalence_of_kanEquivalenceLifting
