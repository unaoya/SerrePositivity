module

public import SerrePositivity.KST.LocalizingInvariants.LaxDifferenceUnitComponents
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FunctorHomSquareRealization

/-!
概要：差の単位の二成分と両端の元の矢印を固定した、実際の coherent な正方形。
方針：C 枝の零性と、可逆余単位で相殺した D 枝の零合成を h Fun で比較し実現する。
規約：写像空間の同値性は後続。使われ方：元の lax pullback 内の単位の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
local instance unitSquareFunctorZero (A X : SSet.{u}) [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex X] :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex ((ihom A).obj X) := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.functorHasZeroVertex A X
local instance unitSquareFunctorZeroMorphisms (A X : SSet.{u})
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex X] : HasZeroMorphisms ((ihom A).obj X).HomotopyCategory :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.hasZeroMorphisms_ho

variable {C D E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)
  {v : E.obj ⟶ D.obj} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction q.hom v) (hv : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful v)

include hv in
lemma laxDifferenceUnitSquare_comm :
    Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (laxArrowHomotopy p q)) ≫
        Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
          (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (laxDifferenceUnitDHomotopy p q v a) q.hom)) =
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (laxDifferenceUnitCHomotopy p q v) p.hom)) ≫
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (laxDifferenceUnitTargetArrowHomotopy p q v)) := by
  have hr : Arrow.mk
      ((hoFunctor.map ((ihom (laxCategory p q).obj).map q.hom)).toFunctor.map
        (laxDifferenceUnitD p q a)) =
      Arrow.mk (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (laxDifferenceUnitDHomotopy p q v a) q.hom))) := by
    have h := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy (laxDifferenceUnitD p q a)) q.hom
    rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy_hom] at h
    exact (congrArg Arrow.mk h).symm.trans
      (Truncated.HomotopyCategory.congr_arrowMk_homMk _ _ rfl)
  have hz := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Lax.comp_zero_of_arrowMk_eq (laxArrowHom p q) _
    (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (laxArrowHomotopy p q))) _ rfl hr (laxDifferenceUnitD_nullComposite p q a hv)
  have ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
      (((laxDifference p q ≫ laxDifferenceRho p q v) ≫ (laxFst p q).hom) ≫ p.hom)) :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isInitialVertex_functorVertex_of_pointwise _
      (fun x => (laxDifferenceUnit_target_fst_post_zero p q v x).1),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isTerminalVertex_functorVertex_of_pointwise _
        (fun x => (laxDifferenceUnit_target_fst_post_zero p q v x).2)⟩
  have hl := ht.isZeroHo.eq_zero_of_tgt
    (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (laxDifferenceUnitCHomotopy p q v) p.hom)))
  rw [hz, hl, zero_comp]

/-- 四つの元の代表ホモトピーを境界として保持する関手正方形。 -/
def laxDifferenceUnitSquare : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomSquare (laxArrowHomotopy p q)
    (laxDifferenceUnitTargetArrowHomotopy p q v)
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (laxDifferenceUnitCHomotopy p q v) p.hom)
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (laxDifferenceUnitDHomotopy p q v a) q.hom) :=
  Classical.choice (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonempty_functorHomSquare_of_homEq _ _ _ _
    (laxDifferenceUnitSquare_comm p q a hv))

end SerrePositivity.KST.LocalizingInvariants
