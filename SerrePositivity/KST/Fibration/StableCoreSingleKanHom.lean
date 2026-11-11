module
public import SerrePositivity.KST.Fibration.CoreSingleKanCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.NerveHomEdgeNaturality

/-! # 元の core S 実現の射を、同じ全 Hom・同じ coherent 辺から回収する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants

namespace SerrePositivity.KST.Fibration
variable {C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} (f : C ⟶ D)

/-- 元の完全射の core S 実現の同じ Ex∞ 射を、正規化した Kan 値間の射として読む。 -/
def stableCoreSingleKanMap :
    stableCoreSingleKanEnrichedFunctor.obj C ⟶ stableCoreSingleKanEnrichedFunctor.obj D :=
  exInfinityKanMap (simplicialDiagonalFunctor.map (coreSExactMap f))

/-- 一回の反復実現の全 Hom から、同じ元の Ex∞ 射を回収する。 -/
theorem stableMultiSingleKan_hom :
    eHomEquiv SSet f ≫ (stableMultiKanEnrichedFunctor 0).map C D =
      eHomEquiv SSet (show (stableMultiKanEnrichedFunctor 0).obj C ⟶
        (stableMultiKanEnrichedFunctor 0).obj D from
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map ((multiRealizationFunctor 1).map (stableExactInputMap f))) := by
  change eHomEquiv SSet f ≫ ((stableMultiRealizationEnrichedFunctor 1).map C D ≫
    exInfinityClosedKanEnrichedFunctor.map _ _) = _
  rw [← Category.assoc, stableMultiRealizationEnrichedFunctor_hom]
  exact exInfinityClosedKanEnrichedFunctor_hom
    (X := (stableMultiRealizationEnrichedFunctor 1).obj C)
    (Y := (stableMultiRealizationEnrichedFunctor 1).obj D)
    ((multiRealizationFunctor 1).map (stableExactInputMap f))

/-- 対象座標の読み替え後も、同じ元の完全射の core S 実現射を回収する。 -/
theorem stableCoreSingleKan_hom :
    eHomEquiv SSet f ≫ stableCoreSingleKanEnrichedFunctor.map C D =
      eHomEquiv SSet (stableCoreSingleKanMap f) := by
  have hg := relabelEnrichedObjects_hom (stableMultiKanEnrichedFunctor 0)
    stableCoreSingleKanObject (funext stableCoreSingleKan_object_eq) f _
      (stableMultiSingleKan_hom f)
  have he : eqToHom (stableCoreSingleKan_object_eq C).symm ≫
      (show (stableMultiKanEnrichedFunctor 0).obj C ⟶
        (stableMultiKanEnrichedFunctor 0).obj D from
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map ((multiRealizationFunctor 1).map (stableExactInputMap f))) ≫
      eqToHom (stableCoreSingleKan_object_eq D) = stableCoreSingleKanMap f := by
    rw [← coreSingleKanIso_hom_eq, ← coreSingleKanIso_inv_eq]
    have hn := coreSingleKanIso_naturality (C := C) (D := D) f
    rw [← Category.assoc, ← hn]
    change (stableCoreSingleKanMap f ≫ (coreSingleKanIso D).hom) ≫
      (coreSingleKanIso D).inv = stableCoreSingleKanMap f
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact hg.trans (congrArg (eHomEquiv SSet) he)

/-- 元の core S の同じ射を、同じ coherent な一単体として回収する。 -/
theorem stableCoreSingleKan_edge :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap stableCoreSingleKanEnrichedFunctor).app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow f).edge = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (stableCoreSingleKanMap f)).edge :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveMap_edge_of_homEquiv _ _ _ (stableCoreSingleKan_hom f)

/-- 一回の反復実現の全 ∞ 関手でも、元の core S の Ex∞ 射の同じ辺を回収する。 -/
theorem stableMultiSingleKan_edge :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0)).app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow f).edge = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (stableCoreSingleKanMap f)).edge := by
  rw [← stableCoreSingleKanInfinity_eq]
  exact stableCoreSingleKan_edge f

end SerrePositivity.KST.Fibration
