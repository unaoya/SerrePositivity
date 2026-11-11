module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceFibration
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.KanFibrationEquivalence

/-!
概要：充満忠実な inner fibration の右写像空間の相対可縮性。
方針：写像空間の全ホーン持ち上げ性と実際のホモトピー逆から全境界を持ち上げる。
規約：充満忠実性は A3e の pinched 写像空間での定義。
使われ方：Kerodon Proposition 4.8.4.5（Tag 05AR） の主同値判定への還元。

対応節は Kerodon 4.8（Tag 0578）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors

/-- 概要：充満忠実な inner fibration の右写像空間の射は trivial Kan fibration。
方針：ホモトピー逆と全ホーンの rlp から全境界の rlp を得る。
規約：始域と終域は quasicategory。
使われ方：Kerodon Proposition 4.8.4.5（Tag 05AR） の相対的な写像空間。 -/
lemma IsFullyFaithful.pinchedHomMap_trivialKanFibration {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {p : X ⟶ Y} [InnerFibration p]
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful p) (x y : X _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap p x y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.trivialKanFibration_of_fibration_of_simplicialHomotopyEquivalence _ (hp x y)

/-- 概要：充満忠実な inner fibration の写像空間の射の全ての fiber は可縮な Kan 複体。
方針：写像空間の射の trivial Kan fibration 性を頂点上の fiber に適用する。
規約：fiber を取る写像空間の辺の頂点は任意。
使われ方：Kerodon Proposition 4.8.4.5（Tag 05AR） の標準単体への引き戻し。 -/
lemma IsFullyFaithful.pinchedHomMap_vertexFiber_isContractibleKan {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {p : X ⟶ Y} [InnerFibration p]
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful p) (x y : X _⦋0⦌)
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (p.app (Opposite.op ⦋0⦌) x) (p.app (Opposite.op ⦋0⦌) y)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap p x y) s) := by
  have := hp.pinchedHomMap_trivialKanFibration x y
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_isContractibleKan _ _

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
