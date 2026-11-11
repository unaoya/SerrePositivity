module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallLeftUnstraightening
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ContinuousKanFilling
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ContinuousKanSequence

/-!
分割で生成：docstring を書き直すこと
概要：一般 coherent な filtered 空間値図式の全空間模型を元の値から有限検出する。
方針：小さい unstraightening の Kan 置換を取り、fiber の値との同値を合成する。
規約：頂点ごとの比較射だけを構成する。余錐全体と余極限の普遍性は後続の証明課題。
使われ方：strict 図式を仮定しない filtered 余極限の模型の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {B : SSet.{u}}

/-- 概要：一般 coherent な空間値図式の小さい全空間の Kan 置換。
方針：既存の小さい left unstraightening を具体的な連続置換で送る。
規約：余極限性を定義の一部として要求しない。使われ方：一般図式の候補模型。 -/
def coherentDiagramTotalKan
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening F)

/-- 概要：全空間の置換は Kan 複体。
方針：具体的な連続置換の充填性を使う。
規約：底の filtered 性は不要。使われ方：有限射のホモトピー類の比較。 -/
instance coherentDiagramTotalKan_kanComplex
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    KanComplex (coherentDiagramTotalKan F) :=
  inferInstanceAs (KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening F)))

end SerrePositivity.InfinityCategories.Project.FilteredExchange
