module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovPresentedMappingCone
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.NerveConeCoherentComparison
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseUniversalSquares

/-!
概要：元の Postnikov 提示錐の実 AW 写像像が空間値の極限錐であることを示す。
方針：通常の像錐の底の極限性と実 class の fibration を適用し、P-8 の全錐等式で戻す。
規約：頂点・脚だけで比較せず、同じ元の nerve 錐の全高次資料を保持する。
使われ方：指定局所化の表現可能 Hom 比較が届いた後の f4d の極限検出。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open SSet.modelCategoryQuillen
open CategoryTheory Limits MonoidalCategory Opposite HomotopicalAlgebra
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (A B : Mon (Complex R)) [B.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n)

set_option maxHeartbeats 800000 in -- 元の提示錐とその通常の像錐の型を照合する。
def postnikovPresentedCellMappingRawCone_underlying_isLimit :
    IsLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.mapCone
      ((multiplicativeCellMappingInfinityKanFunctor R A).mapCone
        (postnikovInfinityPresentedCone R B n hn))) := by
  have transport {F G : PostnikovInfinityShape.{u} ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u + 1}}
      (α : F ≅ G) (c : Cone F) (d : Cone G)
      (e : (Cone.postcompose α.hom).obj c ≅ d)
      (hd : IsLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.mapCone d)) :
      IsLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.mapCone c) := by
    have hp : IsLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.mapCone ((Cone.postcompose α.hom).obj c)) :=
      hd.ofIsoLimit ((Cone.functoriality G _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget).mapIso e).symm
    have ht : IsLimit ((Cone.postcompose (Functor.whiskerRight α.hom _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.mapCone c)) :=
      hp.ofIsoLimit (Functor.mapConePostcompose _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)
    exact IsLimit.postcomposeHomEquiv (Functor.isoWhiskerRight α _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) _ ht
  exact transport (eqToIso (postnikovPresentedCellMappingDiagram R A B n hn))
    ((multiplicativeCellMappingInfinityKanFunctor R A).mapCone
      (postnikovInfinityPresentedCone R B n hn))
    (postnikovCellLargeKanCone R A B n hn)
    (postnikovPresentedCellMappingConeIso R A B n hn)
    (postnikovCellLargeKanCone_underlying_isLimit R A B n hn)

set_option maxHeartbeats 800000 in -- 元の全図式上で class の実 fibration を評価する。
lemma postnikovPresentedCellMappingRawCone_space_isLimit :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone
      ((multiplicativeCellMappingInfinityKanFunctor R A).mapCone
        (postnikovInfinityPresentedCone R B n hn))) := by
  have := postnikovCellMappingClass_fibration R A B n hn
  have : Fibration
      (show ((multiplicativeCellMappingLargeKanFunctor R A).obj
          (postnikovPerturbedExtension R B n hn)).obj ⟶
        ((multiplicativeCellMappingLargeKanFunctor R A).obj
          (postnikovDerivationTarget R B n hn)).obj from
        (multiplicativeCellMappingLargeKanFunctor R A).map (postnikovPerturbedClass R B n hn)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.fibration_uliftFunctor_map
      (multiplicativeMappingPostcompose R (cellResolution R A) (postnikovPerturbedClass R B n hn))
  have : ∀ Z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u + 1}, Fibration
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (postnikovInfinityCospan R B n hn ⋙
        multiplicativeCellMappingInfinityKanFunctor R A) Z).map
        (AsSmall.up.map WalkingCospan.Hom.inl)) := fun Z => by
    change Fibration (((SimplicialCategory.sHomFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u + 1}).obj (op Z)).map
      ((multiplicativeCellMappingLargeKanFunctor R A).map (postnikovPerturbedClass R B n hn)))
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanObjectHom_map_fibration Z _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.strictCoherentCone_isLimit_of_cospan_homLimit
    ((multiplicativeCellMappingInfinityKanFunctor R A).mapCone
      (postnikovInfinityPresentedCone R B n hn))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanObjectHomCone_isLimit_of_forget _
      (postnikovPresentedCellMappingRawCone_underlying_isLimit R A B n hn))

lemma postnikovPresentedCellMappingImageCone_isLimit :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (multiplicativeCellMappingInfinityCoherent R A)
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u + 1, u + 2}
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone (postnikovInfinityPresentedCone R B n hn)))) := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isLimitCone_iff_of_val_eq _ _
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uliftNerveCone_coherent_eq (postnikovInfinityPresentedCone R B n hn)
      (multiplicativeCellMappingInfinityKanFunctor R A))).mpr
  exact postnikovPresentedCellMappingRawCone_space_isLimit R A B n hn

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
