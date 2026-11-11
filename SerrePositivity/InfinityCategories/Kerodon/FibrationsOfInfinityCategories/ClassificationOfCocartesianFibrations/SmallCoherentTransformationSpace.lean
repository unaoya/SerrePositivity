module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TransformationSmallness
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallLeftUnstraighteningMappingSpace
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallSimplicialMap
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.UniverseKan

/-!
概要：小さい coherent な変換空間と、小さい fibration の相対写像空間への比較射。
方針：変換の各次数を縮小し、標準同型を使って比較射を元の宇宙へ降ろす。
規約：完全忠実性そのものは未証明であり、元の比較の同値性との同値を示す。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、同じ宇宙の Kan な写像空間での比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：小さい底上の coherent な二図式の変換空間の小さい代表。
方針：端点固定による小ささを使い、区間写像空間を各次数で縮小する。
規約：底は任意の小さい単体集合。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、fibration の小さい写像空間と比較する始域。 -/
noncomputable def smallLeftUnstraighteningTransformationSpace {B : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallSimplicialSet.{u, u + 1} (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace F G)

/-- 概要：小さい変換空間の持ち上げは元の区間模型の変換空間と同型。
方針：各次数の縮小の標準同型を使う。
規約：ホモトピー同値でなく厳密な同型。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、元の unstraightening の写像空間比較を移す。 -/
noncomputable def smallLeftUnstraighteningTransformationSpaceIso {B : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj (smallLeftUnstraighteningTransformationSpace F G) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace F G :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallSimplicialSetIso.{u, u + 1} (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace F G)

/-- 概要：小さい coherent な変換空間は Kan 複体。
方針：縮小同型で Kan 性を持ち上げた代表へ移し、既存の宇宙反映を使う。
規約：底の quasicategory 性を仮定しない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、小さい写像空間の同値の判定。 -/
instance smallLeftUnstraighteningTransformationSpace_kanComplex {B : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    KanComplex (smallLeftUnstraighteningTransformationSpace F G) := by
  have : KanComplex ((SSet.uliftFunctor.{u + 1, u}).obj
      (smallLeftUnstraighteningTransformationSpace F G)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanComplex_of_iso (smallLeftUnstraighteningTransformationSpaceIso F G).symm
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.kanComplex_of_ulift.{u + 1, u} _

/-- 概要：小さい coherent な変換空間から小さい unstraightening 間の相対写像空間への比較射。
方針：元の比較射を始域と標的の標準同型で移し、宇宙を降ろす。
規約：始域も標的も宇宙 u の Kan 複体。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、完全忠実性を同じ宇宙の実際の射として扱う。 -/
noncomputable def smallLeftUnstraighteningMappingSpaceMap {B : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    smallLeftUnstraighteningTransformationSpace F G ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection G)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftMorphismDown ((smallLeftUnstraighteningTransformationSpaceIso F G).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.liftedSmallLeftUnstraighteningMappingSpaceMap F G)

/-- 概要：小さい写像空間比較の持ち上げは元の比較射と可換。
方針：宇宙を降ろして持ち上げる往復と、相対写像空間の縮小同型の往復を消す。
規約：元の比較射を変更せずに移送する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、元の比較の評価を小さい比較へ移す。 -/
lemma smallLeftUnstraighteningMappingSpaceMap_comparison {B : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningMappingSpaceMap F G) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningRelativeFunctorIso F G).hom =
    (smallLeftUnstraighteningTransformationSpaceIso F G).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMappingSpaceMap F G := by
  rw [smallLeftUnstraighteningMappingSpaceMap, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftMorphismDown_lift, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.liftedSmallLeftUnstraighteningMappingSpaceMap_comparison]

/-- 概要：小さい写像空間比較の同値性は元の比較の同値性と同値。
方針：Kan 複体間の同値の宇宙反映と、両端の標準同型の二対三則を使う。
規約：完全忠実性の未証明の核心はこの移送では仮定も解消もしない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、元の比較に関する証明を小さい fibration の Hom へ移す。 -/
lemma smallLeftUnstraighteningMappingSpaceMap_isQCatEquivalence_iff {B : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (smallLeftUnstraighteningMappingSpaceMap F G) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMappingSpaceMap F G) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.isQCatEquivalence_ulift_iff_of_kan
    (smallLeftUnstraighteningMappingSpaceMap F G)]
  have hS : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (smallLeftUnstraighteningTransformationSpaceIso F G).hom :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (smallLeftUnstraighteningTransformationSpaceIso F G)).isQCatEquivalence
  have hT : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningRelativeFunctorIso F G).hom :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningRelativeFunctorIso F G)).isQCatEquivalence
  constructor
  · intro h
    apply hS.cancel_left
    rw [← smallLeftUnstraighteningMappingSpaceMap_comparison]
    exact h.comp hT
  · intro h
    apply hT.cancel_right
    rw [smallLeftUnstraighteningMappingSpaceMap_comparison]
    exact hS.comp h

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
