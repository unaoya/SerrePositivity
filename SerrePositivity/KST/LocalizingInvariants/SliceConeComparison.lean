module

public import SerrePositivity.KST.LocalizingInvariants.FunctorHomWhiskering
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluationNaturality
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FunctorHoEvaluation
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.NativeConeFamilyEvaluation

/-!
概要：同じ図式上の slice の比較辺を、頂点射と底の恒等性を保つ全錐の比較にする。
方針：既存の native な全錐族へ写し、頂点評価と図式制限の全一単体を照合する。
規約：比較辺そのものを保持。使われ方：置換済み fiber と実 fiber の全図式比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.SliceConeComparison

lemma evaluate_arrow {A X : SSet.{u}} [Quasicategory X] {F G : A ⟶ X}
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F G) (x : A _⦋0⦌) :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate α x) =
      Arrow.mk ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) x)).toFunctor.map α) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorCellToNatTrans_app_eq_evaluate]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.functorCellToNatTrans, NatTrans.comp_app, eqToHom_app, eqToHom_refl,
    Category.id_comp, Category.comp_id]
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.functorHomotopyEvaluation_map_app_arrow α x

variable {K X : SSet.{u}} {p : K ⟶ X} {c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p} (e : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p).Edge c d)

def hom : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom c.val d.val :=
  Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeConeFunctorEdge e).toTruncated

lemma apex_arrow [Quasicategory X] :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (hom e) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.joinApexVertex K)) =
      Arrow.mk (Truncated.HomotopyCategory.homMk
        (e.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p)).toTruncated) := by
  rw [evaluate_arrow]
  apply Truncated.HomotopyCategory.congr_arrowMk_homMk
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeConeFunctorEdge_apex e

lemma base_arrow : Arrow.mk (homPre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] K) (hom e)) =
    Arrow.mk (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p))) := by
  have he : ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeConeFunctorEdge e).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X)).edge =
      (SSet.Edge.id (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)).edge :=
    congrArg (fun f ↦ f.app (Opposite.op ⦋1⦌) e.edge)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeConeFunctorFamily_restriction p)
  have hh := Truncated.HomotopyCategory.congr_arrowMk_homMk
    (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeConeFunctorEdge e).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X)).toTruncated)
    (SSet.Edge.id (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)).toTruncated he
  rw [SSet.Edge.toTruncated_id, Truncated.HomotopyCategory.homMk_id] at hh
  exact hh

lemma hom_isIso (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) e.toTruncated) : IsIso (hom e) := by
  have h := he.map (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeConeFunctorFamily p)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := (e.map (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeConeFunctorFamily p)).toTruncated)
    (f := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeConeFunctorEdge e).toTruncated) rfl).mp h

def iso (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) e.toTruncated) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso c.val d.val := by
  let : IsIso (hom e) := hom_isIso e he
  exact asIso (hom e)

end SerrePositivity.KST.LocalizingInvariants.SliceConeComparison
