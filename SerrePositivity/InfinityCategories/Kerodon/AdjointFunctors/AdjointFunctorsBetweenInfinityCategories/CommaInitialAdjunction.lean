module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CommaUnitTransportComparison
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CommaSectionInitialUnit
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingAdjunction

/-!
概要：各 comma の始対象から指定単位の写像空間の普遍性と ∞ 随伴を構成する。
方針：同じ始対象からの普遍輸送の同値性を、元の単位比較へ反映する。
規約：全パラメータの単位 Hom の全単射は仮定しない。
使われ方：HTT §5.2.2 の局所存在判定、局所置換から反射への接続。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
variable {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
variable {F : X ⟶ Y} {G : Y ⟶ X}

/-- comma の指定単位の始対象性から、元の標準区間比較そのものの同値性が従う。 -/
lemma unitIntervalMap_isQCatEquivalence_of_commaInitial
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)) (hη : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaInitialCondition η)
    (x : X _⦋0⦌) (y : Y _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitIntervalMap η x y) := by
  have hi := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaInitialCondition_iff η).mp hη x
  have ht := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.parametrizedFiberTransport_evaluate_isQCatEquivalence_of_initialFiberPoint
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberProjection G x) (F.app (Opposite.op ⦋0⦌) x) y
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unitCommaSectionTargetFiberVertex η x) hi
  have he := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberIntervalIso G x y)).isQCatEquivalence
  exact (ht.comp he).ofFunctorIso (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unitIntervalMap_commaTransportIso η x y).symm

/-- comma の始対象条件は、指定単位の各点の標準写像空間条件を与える。 -/
lemma unitMappingSpaceCondition_of_commaInitial
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)) (hη : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaInitialCondition η) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition η := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitMappingSpaceCondition_iff_interval η).mpr
  intro x y
  exact (unitIntervalMap_isQCatEquivalence_of_commaInitial η hη x y).isSimplicialHomotopyEquivalence

/-- 指定単位が comma の普遍矢印である条件は、標準写像空間の同値条件と同値。 -/
lemma unitCommaInitialCondition_iff_unitMappingSpaceCondition
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaInitialCondition η ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition η :=
  ⟨unitMappingSpaceCondition_of_commaInitial η,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition.unitCommaInitialCondition⟩

/-- 元の指定単位を持つ随伴の存在は、その単位の comma 始対象条件と同値。 -/
lemma qcat_exists_adjunction_unitHom_iff_commaInitial
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)) :
    (∃ a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G, a.unitHom = η) ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaInitialCondition η :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcat_exists_adjunction_unitHom_iff_unitMappingSpaceCondition η).trans
    (unitCommaInitialCondition_iff_unitMappingSpaceCondition η).symm

/-- 各始域の comma に始対象があれば、G は ∞ 右随伴。 -/
lemma exists_qcatAdjunction_of_commaFiberInitial (G : Y ⟶ X)
    (h : ∀ x : X _⦋0⦌, ∃ v : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex v) :
    ∃ F : X ⟶ Y, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G) := by
  obtain ⟨F, η, hη⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.exists_unit_initialCondition_of_fiberInitial G h
  exact ⟨F, ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatAdjunctionOfUnitMappingSpaceCondition η
    (unitMappingSpaceCondition_of_commaInitial η hη)⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
