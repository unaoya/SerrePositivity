module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallUnstraighteningMappingEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallCoherentTransformationSpace

/-!
概要：小さい底上の写像空間比較の同値性を pinched 模型と小さい宇宙へ移す。
方針：既存の厳密な比較同型と宇宙反映の同値条件を適用する。
規約：実際の比較射の同値性を与え追加の比較仮定を置かない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T） の小さい底上の公開界面。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：小さい底上の標準 pinched 写像空間の unstraightening 比較は同値。
方針：区間模型との既証明の同値条件へ主定理を渡す。
規約：図式は任意の coherent な空間値図式。
使われ方：標準写像空間による完全忠実性の入力。 -/
lemma small_leftUnstraighteningPinchedMappingSpaceMap_isQCatEquivalence
    {B : SSet.{u + 1}} [∀ n, Small.{u} (B.obj n)] (F G : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningPinchedMappingSpaceMap F G) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningPinchedMappingSpaceMap_isQCatEquivalence_iff F G).mpr
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.small_leftUnstraighteningMappingSpaceMap_isQCatEquivalence F G)

/-- 概要：宇宙を持ち上げた小さい相対写像空間への比較射は同値。
方針：元の実際の比較射との厳密な同値条件を使う。
規約：底の quasicategory 性は不要。
使われ方：小さい left fibration の相対 Hom の比較。 -/
lemma liftedSmallLeftUnstraighteningMappingSpaceMap_isQCatEquivalence {B : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.liftedSmallLeftUnstraighteningMappingSpaceMap F G) := by
  have : ∀ n, Small.{u} (((SSet.uliftFunctor.{u + 1, u}).obj B).obj n) :=
    fun n ↦ inferInstanceAs (Small.{u} (ULift.{u + 1} (B.obj n)))
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.liftedSmallLeftUnstraighteningMappingSpaceMap_isQCatEquivalence_iff F G).mpr
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.small_leftUnstraighteningMappingSpaceMap_isQCatEquivalence F G)

/-- 概要：小さい宇宙へ縮小した実際の写像空間比較も同値。
方針：宇宙反映と比較同型による既証明の同値条件を使う。
規約：射の存在だけでなく定義済みの比較射について述べる。
使われ方：小さい coherent 図式と小さい left fibration の写像空間の比較。 -/
lemma smallLeftUnstraighteningMappingSpaceMap_isQCatEquivalence {B : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningMappingSpaceMap F G) := by
  have : ∀ n, Small.{u} (((SSet.uliftFunctor.{u + 1, u}).obj B).obj n) :=
    fun n ↦ inferInstanceAs (Small.{u} (ULift.{u + 1} (B.obj n)))
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningMappingSpaceMap_isQCatEquivalence_iff F G).mpr
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.small_leftUnstraighteningMappingSpaceMap_isQCatEquivalence F G)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
