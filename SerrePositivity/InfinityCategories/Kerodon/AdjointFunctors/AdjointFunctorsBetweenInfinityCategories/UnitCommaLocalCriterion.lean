module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IntervalMappingContractible
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UniversalUnitComma
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.PointwiseUnitComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.EquivalenceAllLimits

/-!
概要：局所存在判定の二つの可縮性条件を具体的に記述する。
方針：comma の始対象条件を左写像空間へ移し、単位比較は path 置換して fiber を取る。
規約：二つの模型の比較は本ファイルでは構成せず、strict fiber の可縮性も主張しない。
使われ方：Kerodon Cor 6.2.6.5（Tag 02FX） の逆方向で残る写像空間比較の両側を固定する。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 概要：単位の comma 始対象条件は左写像空間の可縮性で判定できる。
方針：各始域での始対象性と左 pinched 模型の判定を組み合わせる。
規約：w は指定した x 上の comma fiber の任意の頂点。
使われ方：普遍矢印性を導来 fiber の可縮性へ接続する目標。 -/
lemma unitCommaInitialCondition_iff_mappingSpaces {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaInitialCondition η ↔ ∀ (x : X _⦋0⦌)
      (w : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌),
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSectionVertex η x) w) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaInitialCondition_iff]
  constructor
  · intro h x
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isInitialVertex_iff_pinchedHomLeft_isContractibleKan _).mp (h x)
  · intro h x
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isInitialVertex_iff_pinchedHomLeft_isContractibleKan _).mpr (h x)

/-- 概要：各点の標準単位比較の、指定した点での導来 fiber。
方針：可逆 path で比較射を置換してから頂点上の fiber を取る。
規約：単位比較自体の strict fiber とは区別する。
使われ方：comma の正方形の写像空間と比較すべき可縮な模型。 -/
noncomputable def unitIntervalComparisonFiber {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (b : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x (G.app (Opposite.op ⦋0⦌) y)) _⦋0⦌) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitIntervalMap η x y)) b

/-- 概要：各点の写像空間条件は標準単位比較の全ての導来 fiber の可縮性を与える。
方針：pinched 条件を区間模型へ移し、同値な path 置換の全境界の持ち上げを使う。
規約：比較射が Kan fibration であるという追加仮定を置かない。
使われ方：Cor 6.2.6.5 の逆方向で必要な可縮性の供給。 -/
lemma UnitMappingSpaceCondition.unitIntervalComparisonFiber_isContractibleKan
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} {η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)}
    (hη : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition η) (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (b : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x (G.app (Opposite.op ⦋0⦌) y)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (unitIntervalComparisonFiber η x y b) := by
  have he := ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitMappingSpaceCondition_iff_interval η).mp hη x y).isQCatEquivalence
  have := he.equivalencePathReplacementMap_trivialKanFibration
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_isContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitIntervalMap η x y)) b

/-- 概要：単位の comma 始対象条件を区間写像空間で判定する。
方針：指定単位の頂点の始対象性と反転を用いた区間模型の判定を合わせる。
規約：区間模型は正方形の族の厳密な表示を持つ同じ模型。
使われ方：正方形の可縮性から普遍矢印性を結論する。 -/
lemma unitCommaInitialCondition_iff_intervalMappingSpaces {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaInitialCondition η ↔ ∀ (x : X _⦋0⦌)
      (w : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌),
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSectionVertex η x) w) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaInitialCondition_iff]
  constructor
  · intro h x
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isInitialVertex_iff_intervalMappingSpace_isContractibleKan _).mp (h x)
  · intro h x
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isInitialVertex_iff_intervalMappingSpace_isContractibleKan _).mpr (h x)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
