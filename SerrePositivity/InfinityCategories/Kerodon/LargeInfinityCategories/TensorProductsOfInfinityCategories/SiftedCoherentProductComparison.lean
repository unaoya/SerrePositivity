module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentProductTotalEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SiftedProductComparison
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentTotalObject

/-!
概要：coherent な点ごとの積の元の余極限 Kan 模型から、二つの元の余極限模型の積へ比較する。
方針：小さい全空間の指定比較の Kan 置換に、元の二射影の積比較を続ける。
規約：両脚と単位は元の射を保持。使われ方：sifted 余極限の有限積保存の native な錐への接続。

対応節は Kerodon 9.7（Tag 06ZD）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories
attribute [local instance] _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanTensor_isKan
variable {B : SSet.{u}}
  (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})

/-- 元の coherent 余極限 Kan 模型における、指定二射影の積比較。 -/
def coherentProductTotalKanComparison :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProduct F G) ⟶
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan F ⊗ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan G :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProductTotalComparison F G) ≫
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.totalKanProductComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection F)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection G)

/-- 元の比較の第一脚は、指定第一射影の全空間作用の Kan 置換そのもの。 -/
lemma coherentProductTotalKanComparison_fst :
    coherentProductTotalKanComparison F G ≫
      fst (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan F) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan G) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProductTotalFst F G) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan]
  rw [coherentProductTotalKanComparison, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.totalKanProductComparison,
    Category.assoc, lift_fst, ← Functor.map_comp,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProductTotalComparison_fst]

/-- 元の比較の第二脚も、指定第二射影の全空間作用の Kan 置換そのもの。 -/
lemma coherentProductTotalKanComparison_snd :
    coherentProductTotalKanComparison F G ≫
      snd (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan F) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan G) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProductTotalSnd F G) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan]
  rw [coherentProductTotalKanComparison, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.totalKanProductComparison,
    Category.assoc, lift_snd, ← Functor.map_comp,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProductTotalComparison_snd]

/-- 比較は、元の二つの全空間作用と元の Kan 置換の単位に厳密に整合する。 -/
lemma coherentProductTotalKanComparison_unit :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProduct F G)) ≫
      coherentProductTotalKanComparison F G =
        lift (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProductTotalFst F G ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening F))
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProductTotalSnd F G ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening G)) := by
  apply CartesianMonoidalCategory.hom_ext
  · erw [Category.assoc, coherentProductTotalKanComparison_fst, lift_fst]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.naturality _).symm
  · erw [Category.assoc, coherentProductTotalKanComparison_snd, lift_snd]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.naturality _).symm

/-- sifted な任意の底上で、元の coherent 積図式の余極限 Kan 比較は弱ホモトピー同値。 -/
lemma coherentProductTotalKanComparison_isWeakHomotopyEquivalence [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.IsSiftedInfinity B] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (coherentProductTotalKanComparison F G) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.continuousKanReplacement_map_isWeakHomotopyEquivalence _
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProductTotalComparison_isWeakHomotopyEquivalence F G)).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.totalKanProductComparison_isWeakHomotopyEquivalence_of_sifted _ _)

/-- 同じ元の余極限 Kan 比較は、実際の単体的ホモトピー逆を持つ。 -/
lemma coherentProductTotalKanComparison_homotopyEquivalence [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.IsSiftedInfinity B] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (coherentProductTotalKanComparison F G) :=
  (coherentProductTotalKanComparison_isWeakHomotopyEquivalence F G).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories
