module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.RelativeOverPre
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeFunctorPullbackRestriction
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.GrothendieckConstruction.UniversePullbacks

/-!
概要：持ち上げた実際の相対 Hom 引き戻しの同値性を、元の宇宙へ反映する。
方針：相対引き戻しを始域制限へ移し、引き戻しの宇宙同型と前合成の自然性を使う。
規約：底は quasicategory、標的の射影は left fibration。制限先の充填性は不要。
使われ方：一般の小さい底上の straightening の充満忠実性を閉じる。

対応節は Kerodon 4.9（Tag 03PP）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories

/-- 同じ底上の引き戻した始域は、宇宙移送と厳密な底上の同型で比較できる。 -/
def uliftRelativePullbackSourceIso {E B D : SSet.{u}} (p : E ⟶ B) (k : D ⟶ B) :
    Over.mk ((SSet.uliftFunctor.{v, u}).map (pullback.snd p k ≫ k)) ≅
      Over.mk (pullback.snd ((SSet.uliftFunctor.{v, u}).map p)
        ((SSet.uliftFunctor.{v, u}).map k) ≫ (SSet.uliftFunctor.{v, u}).map k) :=
  Over.isoMk (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uliftPullbackIso p k) (by
    change (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uliftPullbackIso.{u, v} p k).hom ≫
      (pullback.snd _ _ ≫ (SSet.uliftFunctor.{v, u}).map k) = _
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uliftPullbackIso_hom_snd, ← Functor.map_comp]
    rfl)

/-- 引き戻しの宇宙同型と同じ第一射影の間の可換性を底上の射として回収する。 -/
lemma uliftRelativePullbackSourceIso_map {E B D : SSet.{u}} (p : E ⟶ B) (k : D ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.uliftOverMorphism.{u, v} (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorPullbackSourceMap p k) =
      (uliftRelativePullbackSourceIso p k).hom ≫
        _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorPullbackSourceMap ((SSet.uliftFunctor.{v, u}).map p)
          ((SSet.uliftFunctor.{v, u}).map k) := by
  apply Over.OverMorphism.ext
  exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uliftPullbackIso_hom_fst p k).symm

local instance {E B D : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (k : D ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (pullback.snd p k) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_snd p k (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p))⟩

/-- 持ち上げた同じ相対 Hom 引き戻しが同値なら、元の作用も同値。 -/
lemma relativeFunctorPullback_isQCatEquivalence_of_ulift
    {E F B D : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) (k : D ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPullback
      ((SSet.uliftFunctor.{v, u}).map p) ((SSet.uliftFunctor.{v, u}).map q)
      ((SSet.uliftFunctor.{v, u}).map k))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPullback p q k) := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorPullback_isQCatEquivalence_iff_sourceRestriction p q k).mpr
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.relativeFunctorOverPre_isQCatEquivalence_of_ulift.{u, v} q
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorPullbackSourceMap p k)
  have hbig := (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorPullback_isQCatEquivalence_iff_sourceRestriction
    ((SSet.uliftFunctor.{v, u}).map p) ((SSet.uliftFunctor.{v, u}).map q)
    ((SSet.uliftFunctor.{v, u}).map k)).mp h
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeFunctorOverPre_isQCatEquivalence ((SSet.uliftFunctor.{v, u}).map q)
    (uliftRelativePullbackSourceIso.{u, v} p k).hom
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uliftPullbackIso p k))
  rw [uliftRelativePullbackSourceIso_map, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre_comp]
  exact hbig.comp he

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories
