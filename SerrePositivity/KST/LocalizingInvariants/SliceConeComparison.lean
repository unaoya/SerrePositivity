module

public import SerrePositivity.KST.LocalizingInvariants.FunctorHomWhiskering
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorHomEvaluationNaturality
public import SerrePositivity.InfinityCategories.Stable.FunctorHoEvaluation
public import SerrePositivity.InfinityCategories.HomotopyLimits.NativeConeFamilyEvaluation

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
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
namespace SerrePositivity.KST.LocalizingInvariants.SliceConeComparison

lemma evaluate_arrow {A X : SSet.{u}} [Quasicategory X] {F G : A ⟶ X}
    (α : FunctorHom F G) (x : A _⦋0⦌) :
    Arrow.mk (functorHomEvaluate α x) =
      Arrow.mk ((hoFunctor.map (evaluateFunctorAt (Y := X) x)).toFunctor.map α) := by
  rw [← functorCellToNatTrans_app_eq_evaluate]
  simp only [functorCellToNatTrans, NatTrans.comp_app, eqToHom_app, eqToHom_refl,
    Category.id_comp, Category.comp_id]
  exact functorHomotopyEvaluation_map_app_arrow α x

variable {K X : SSet.{u}} {p : K ⟶ X} {c d : JoinCone p} (e : (sliceOver p).Edge c d)

def hom : FunctorHom c.val d.val :=
  Truncated.HomotopyCategory.homMk (nativeConeFunctorEdge e).toTruncated

lemma apex_arrow [Quasicategory X] :
    Arrow.mk (functorHomEvaluate (hom e) (joinApexVertex K)) =
      Arrow.mk (Truncated.HomotopyCategory.homMk
        (e.map (sliceOverProjection p)).toTruncated) := by
  rw [evaluate_arrow]
  apply Truncated.HomotopyCategory.congr_arrowMk_homMk
  exact nativeConeFunctorEdge_apex e

lemma base_arrow : Arrow.mk (homPre (joinInr Δ[0] K) (hom e)) =
    Arrow.mk (𝟙 (HomotopyCategory.mk (functorVertex p))) := by
  have he : ((nativeConeFunctorEdge e).map (coneRestriction K X)).edge =
      (SSet.Edge.id (functorVertex p)).edge :=
    congrArg (fun f ↦ f.app (Opposite.op ⦋1⦌) e.edge)
      (nativeConeFunctorFamily_restriction p)
  have hh := Truncated.HomotopyCategory.congr_arrowMk_homMk
    (((nativeConeFunctorEdge e).map (coneRestriction K X)).toTruncated)
    (SSet.Edge.id (functorVertex p)).toTruncated he
  rw [SSet.Edge.toTruncated_id, Truncated.HomotopyCategory.homMk_id] at hh
  exact hh

lemma hom_isIso (he : IsInvertibleEdge (X := sliceOver p) e.toTruncated) : IsIso (hom e) := by
  have h := he.map (nativeConeFunctorFamily p)
  exact (isInvertibleEdge_congr (e := (e.map (nativeConeFunctorFamily p)).toTruncated)
    (f := (nativeConeFunctorEdge e).toTruncated) rfl).mp h

def iso (he : IsInvertibleEdge (X := sliceOver p) e.toTruncated) : FunctorIso c.val d.val := by
  let : IsIso (hom e) := hom_isIso e he
  exact asIso (hom e)

end SerrePositivity.KST.LocalizingInvariants.SliceConeComparison
