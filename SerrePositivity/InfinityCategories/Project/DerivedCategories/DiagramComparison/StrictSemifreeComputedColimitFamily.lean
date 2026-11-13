module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictSemifreeComputedCoconePointwise
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictSemifreeColimitFamily
import all SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictSemifreeColimitFamily
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictSimplexEvaluationAtParameter
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorFamilyTranspose

/-!
概要：同じ計算済み全余錐族を普遍余錐の全部分圏へ制限し、指定の全余錐族へ比較する。
方針：既存の点ごとの余極限性と全評価の自然性で部分複体へ制限する。
規約：別の全余錐族を選び直さず、包含後は元の同じ共同評価に一致する。
使われ方：3b-3 R6 U34〜U37、全指定余錐族とapexの比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet MonoidalCategory MonoidalClosed CartesianMonoidalCategory
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A]

/-- U34の分割：同じ共同評価を、余錐形状の関手単体集合への族で読む。 -/
def strictSemifreeComputedCoconeFunctorMap :
    nerve (StrictSemifreeDiagram A SimplexCategoryᵒᵖ) ⟶
      (ihom (join ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ))
        (Δ[0] : SSet.{u + 1}))).obj (derivedInfinityCategory A) :=
  curry ((β_ (join ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ))
    (Δ[0] : SSet.{u + 1})) (nerve (StrictSemifreeDiagram A SimplexCategoryᵒᵖ))).hom ≫
      strictSemifreeComputedDAJoinFamily A)

/-- U34の前提計算：同じ族の頂点は同じ計算済み余錐を表す。 -/
lemma strictSemifreeComputedCoconeFunctorMap_vertex
    (F : StrictSemifreeDiagram A SimplexCategoryᵒᵖ) :
    (strictSemifreeComputedCoconeFunctorMap A).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ F) =
      functorVertex (strictSemifreeComputedDACoconeAt A F).val := by
  change (transposeFunctorFamily (strictSemifreeComputedFunctorCoconeMap A)).app
    (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ F) = _
  rw [transposeFunctorFamily_vertex]
  have h := strictFamilyCurry_evaluateAt A (Semifree A)
    (strictSemifreeComputedDAJoinFamily A) F
  change curry (uncurry (strictSemifreeComputedFunctorCoconeMap A)) ≫ _ = _ at h
  rw [curry_uncurry] at h
  exact congrArg functorVertex h

/-- U34：同じ全余錐族の像を普遍余錐の全部分圏へ制限する。 -/
def strictSemifreeComputedColimitFamily :
    nerve (StrictSemifreeDiagram A SimplexCategoryᵒᵖ) ⟶
      colimitCocones ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ))
        (derivedInfinityCategory A) := by
  refine SSet.Subcomplex.lift (strictSemifreeComputedCoconeFunctorMap A) ?_
  rintro n s ⟨x, rfl⟩ α
  let I := (SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ)
  let D := derivedInfinityCategory A
  let E := (ihom (join I (Δ[0] : SSet.{u + 1}))).obj D
  change InitialBoundaryLifting (coconeRestriction I D)
    (E.map α.op ((strictSemifreeComputedCoconeFunctorMap A).app n x))
  have hn := ConcreteCategory.congr_hom
    ((strictSemifreeComputedCoconeFunctorMap A).naturality α.op) x
  change (strictSemifreeComputedCoconeFunctorMap A).app (Opposite.op ⦋0⦌)
    ((nerve (StrictSemifreeDiagram A SimplexCategoryᵒᵖ)).map α.op x) =
      E.map α.op ((strictSemifreeComputedCoconeFunctorMap A).app n x) at hn
  rw [← hn]
  obtain ⟨F, hF⟩ := ComposableArrows.mk₀_surjective
    ((nerve (StrictSemifreeDiagram A SimplexCategoryᵒᵖ)).map α.op x)
  rw [hF, strictSemifreeComputedCoconeFunctorMap_vertex]
  exact (strictSemifreeComputedDACoconeAt_isColimit A F).initialBoundaryLifting

/-- 制限後の包含は同じ全余錐族そのものである。 -/
@[reassoc]
lemma strictSemifreeComputedColimitFamily_inclusion :
    strictSemifreeComputedColimitFamily A ≫
      (relativeInitialVertices (coconeRestriction
        ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ))
          (derivedInfinityCategory A))).ι = strictSemifreeComputedCoconeFunctorMap A :=
  SSet.Subcomplex.lift_ι _ _

/-- U34：部分圏への制限後も同じ共同評価を保つ。 -/
lemma strictSemifreeComputedColimitFamily_evaluation :
    (β_ (nerve (StrictSemifreeDiagram A SimplexCategoryᵒᵖ))
      (join ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ)) Δ[0])).hom ≫
      uncurry (strictSemifreeComputedColimitFamily A ≫
        (relativeInitialVertices (coconeRestriction
          ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ))
            (derivedInfinityCategory A))).ι) = strictSemifreeComputedDAJoinFamily A := by
  rw [strictSemifreeComputedColimitFamily_inclusion, strictSemifreeComputedCoconeFunctorMap,
    uncurry_curry, ← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]

/-- U35：同じ普遍余錐族の下方は元の指定全strict図式と厳密に一致する。 -/
lemma strictSemifreeComputedColimitFamily_projection :
    strictSemifreeComputedColimitFamily A ≫
      colimitCoconeProjection ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ))
        (derivedInfinityCategory A) = strictSemifreeDiagramFamily A SimplexCategoryᵒᵖ := by
  change strictSemifreeComputedColimitFamily A ≫ _ ≫
    coconeRestriction ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ))
      (derivedInfinityCategory A) = _
  rw [strictSemifreeComputedColimitFamily_inclusion_assoc]
  apply uncurry_injective
  rw [coconeRestriction, uncurry_pre_app, strictSemifreeComputedCoconeFunctorMap, uncurry_curry,
    strictSemifreeDiagramFamily, uncurry_curry]
  rw [BraidedCategory.braiding_naturality_left_assoc,
    strictSemifreeComputedDAJoinFamily_front]

/-- U36：同じ指定下方図式を持つ二つの全普遍余錐族の同型。 -/
def strictSemifreeComputedColimitFamilyIso :
    FunctorIso (strictSemifreeComputedColimitFamily A)
      (strictSemifreeColimitFamily A SimplexCategoryᵒᵖ) :=
  colimitCoconeFamilyIso (strictSemifreeDiagramFamily A SimplexCategoryᵒᵖ)
    (fun a => smallShape_hasColimit A (nerve SimplexCategoryᵒᵖ)
      ((functorVertexEquiv _ _).symm
        ((strictSemifreeDiagramFamily A SimplexCategoryᵒᵖ).app (Opposite.op ⦋0⦌) a)))
    (strictSemifreeComputedColimitFamily A) (strictSemifreeColimitFamily A SimplexCategoryᵒᵖ)
    (strictSemifreeComputedColimitFamily_projection A)
    (strictSemifreeColimitFamily_projection A SimplexCategoryᵒᵖ)

/-- U37の前提計算：指定の全余錐族は同じ普遍余錐族の包含である。 -/
private lemma specifiedCoconeFamily_eq_aux :
    strictSemifreeCoconeFunctorFamily A SimplexCategoryᵒᵖ =
      strictSemifreeColimitFamily A SimplexCategoryᵒᵖ ≫
        (relativeInitialVertices (coconeRestriction
          ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ))
            (derivedInfinityCategory A))).ι := rfl

/-- U37の定義計算を、証明を介して公開する。 -/
lemma specifiedCoconeFamily_eq :
    strictSemifreeCoconeFunctorFamily A SimplexCategoryᵒᵖ =
      strictSemifreeColimitFamily A SimplexCategoryᵒᵖ ≫
        (relativeInitialVertices (coconeRestriction
          ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ))
            (derivedInfinityCategory A))).ι := by
  exact specifiedCoconeFamily_eq_aux A

/-- U37：同じ比較を全余錐の関手単体集合へ送る。 -/
def strictSemifreeComputedCoconeFamilyIso :
    FunctorIso (strictSemifreeComputedColimitFamily A ≫
      (relativeInitialVertices (coconeRestriction
        ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ))
          (derivedInfinityCategory A))).ι)
      (strictSemifreeCoconeFunctorFamily A SimplexCategoryᵒᵖ) :=
  by
  simpa only [specifiedCoconeFamily_eq] using
    (strictSemifreeComputedColimitFamilyIso A).postcomp
      (relativeInitialVertices (coconeRestriction
        ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ))
          (derivedInfinityCategory A))).ι

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
