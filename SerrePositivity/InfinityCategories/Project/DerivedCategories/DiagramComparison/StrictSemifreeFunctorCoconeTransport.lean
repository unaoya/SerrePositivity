module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictSemifreeRawDAFrontIso
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeCartesianTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.InvertibleCartesian

/-!
概要：元の全native余錐族を、指定strict全評価を前面に持つ全余錐族へ輸送する。
方針：全パラメーターを関手圏に入れ、既存のcartesian余錐の持ち上げを一度使う。
規約：元の可逆な底の辺と全高次単体を保つ。図式ごとの余錐を選び直さない。
使われ方：3b-3 R6 U31〜U32、指定全図式と同じ前面を持つ計算済み余錐族。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet MonoidalCategory MonoidalClosed
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A]

/-- U31の分割：同じraw全余錐族の形状を既存のjoin同型で運ぶ。 -/
def strictSemifreeReindexedRawDAJoinFamily :
    nerve (StrictSemifreeDiagram A SimplexCategoryᵒᵖ) ⊗
      join ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ))
        (Δ[0] : SSet.{u + 1}) ⟶ derivedInfinityCategory A :=
  (nerve (StrictSemifreeDiagram A SimplexCategoryᵒᵖ) ◁ (strictSemifreeJoinShapeIso A).hom) ≫
    strictSemifreeRawDAJoinFamily A

/-- U31の分割：全パラメーターを標的の関手圏へ入れた同じraw余錐。 -/
def strictSemifreeRawFunctorCoconeMap :
    join ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ))
      (Δ[0] : SSet.{u + 1}) ⟶
      (ihom (nerve (StrictSemifreeDiagram A SimplexCategoryᵒᵖ))).obj
        (derivedInfinityCategory A) :=
  curry (strictSemifreeReindexedRawDAJoinFamily A)

/-- U31の分割：指定strict全図式も同じ標的関手圏へ入れる。 -/
def strictSemifreeStrictFunctorDiagram :
    (SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ) ⟶
      (ihom (nerve (StrictSemifreeDiagram A SimplexCategoryᵒᵖ))).obj
        (derivedInfinityCategory A) :=
  curry (strictSemifreeEvaluation A SimplexCategoryᵒᵖ)

/-- U31の同じ底の比較を関手圏へcurryしたもの。 -/
def strictSemifreeRawFunctorDiagramIso :
    FunctorIso
      (joinInl ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ)) Δ[0] ≫
        strictSemifreeRawFunctorCoconeMap A) (strictSemifreeStrictFunctorDiagram A) := by
  have h := (strictSemifreeRawDAFrontIso A).curry
  simpa only [strictSemifreeRawFunctorCoconeMap, strictSemifreeReindexedRawDAJoinFamily,
    strictSemifreeStrictFunctorDiagram, curry_natural_left, Category.assoc] using! h

/-- U31〜U32の分割：指定前面を持つ同じ全余錐の輸送は全関手同型を伴う。 -/
lemma exists_strictSemifreeTransportedFunctorCocone :
    ∃ g : join ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ))
        (Δ[0] : SSet.{u + 1}) ⟶
        (ihom (nerve (StrictSemifreeDiagram A SimplexCategoryᵒᵖ))).obj
          (derivedInfinityCategory A),
      joinInl ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ)) Δ[0] ≫ g =
        strictSemifreeStrictFunctorDiagram A ∧
      Nonempty (FunctorIso g (strictSemifreeRawFunctorCoconeMap A)) := by
  let K := (SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ)
  let X := (ihom (nerve (StrictSemifreeDiagram A SimplexCategoryᵒᵖ))).obj
    (derivedInfinityCategory A)
  let F : join K (Δ[0] : SSet.{u + 1}) ⟶ X := strictSemifreeRawFunctorCoconeMap A
  let q : K ⟶ X := strictSemifreeStrictFunctorDiagram A
  let p := coconeRestriction K X
  let v := functorVertex F
  let b := functorVertex q
  have hv : p.app (Opposite.op ⦋0⦌) v = functorVertex (joinInl K Δ[0] ≫ F) := rfl
  let a0 := FunctorIso.edge ((strictSemifreeRawFunctorDiagramIso A).symm)
  let a : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom K).obj X))
      b (p.app (Opposite.op ⦋0⦌) v) :=
    ⟨a0.edge, a0.src_eq, a0.tgt_eq.trans hv.symm⟩
  have ha : IsInvertibleEdge a :=
    (isInvertibleEdge_congr (e := a) (f := a0) rfl).mpr
      (FunctorIso.edge_isInvertible ((strictSemifreeRawFunctorDiagramIso A).symm))
  obtain ⟨w, e, he, hec⟩ := exists_cartesian_cocone_lift K X v b a
  have him : IsInvertibleEdge (X := (ihom K).obj X)
      (e.map ((truncation 2).map p)) :=
    (isInvertibleEdge_congr (e := e.map ((truncation 2).map p)) (f := a) he).mpr ha
  have hie := isInvertibleEdge_of_isCartesianEdge p e hec him
  let g : join K (Δ[0] : SSet.{u + 1}) ⟶ X := (functorVertexEquiv _ _).symm w
  have hgv : functorVertex g = w := (functorVertexEquiv _ _).apply_symm_apply w
  have hsrc : ((ihom K).obj X).δ 1 (p.app (Opposite.op ⦋1⦌) e.edge) =
      p.app (Opposite.op ⦋0⦌) w := (e.map ((truncation 2).map p)).src_eq
  rw [he] at hsrc
  have hw : p.app (Opposite.op ⦋0⦌) w = b := hsrc.symm.trans a.src_eq
  refine ⟨g, ?_, ⟨?_⟩⟩
  · apply functorVertex_injective
    change p.app (Opposite.op ⦋0⦌) (functorVertex g) = b
    rw [hgv, hw]
  · letI : IsIso (SSet.Truncated.HomotopyCategory.homMk e) := hie
    exact eqToIso (congrArg SSet.HomotopyCategory.mk hgv) ≪≫
      asIso (SSet.Truncated.HomotopyCategory.homMk e)

/-- U31の分割：輸送は全パラメーターの関手圏で一度だけ選ぶ。 -/
def strictSemifreeComputedFunctorCoconeMap :=
  (exists_strictSemifreeTransportedFunctorCocone A).choose

/-- 選んだ同じ全余錐の前面は、指定strict図式と厳密に一致する。 -/
lemma strictSemifreeComputedFunctorCoconeMap_front :
    joinInl ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ)) Δ[0] ≫
      strictSemifreeComputedFunctorCoconeMap A = strictSemifreeStrictFunctorDiagram A :=
  (exists_strictSemifreeTransportedFunctorCocone A).choose_spec.1

/-- U32の分割：同じ輸送の全関手同型。 -/
def strictSemifreeComputedFunctorCoconeIso :
    FunctorIso (strictSemifreeRawFunctorCoconeMap A)
      (strictSemifreeComputedFunctorCoconeMap A) :=
  (exists_strictSemifreeTransportedFunctorCocone A).choose_spec.2.some.symm

/-- U31：同じ全パラメーターのままuncurryした、指定前面の計算済み余錐族。 -/
def strictSemifreeComputedDAJoinFamily := uncurry (strictSemifreeComputedFunctorCoconeMap A)

/-- U31：計算済み余錐族の前面は元の同じstrict全評価。 -/
lemma strictSemifreeComputedDAJoinFamily_front :
    (nerve (StrictSemifreeDiagram A SimplexCategoryᵒᵖ) ◁
      joinInl ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ)) Δ[0]) ≫
      strictSemifreeComputedDAJoinFamily A = strictSemifreeEvaluation A SimplexCategoryᵒᵖ := by
  rw [strictSemifreeComputedDAJoinFamily, ← uncurry_natural_left,
    strictSemifreeComputedFunctorCoconeMap_front]
  exact uncurry_curry _

/-- U32：元の同じraw全余錐族からの、joinの全単体の輸送の同型。 -/
def strictSemifreeComputedDAJoinFamily_transportIso :
    FunctorIso
      ((nerve (StrictSemifreeDiagram A SimplexCategoryᵒᵖ) ◁
        (strictSemifreeJoinShapeIso A).hom) ≫ strictSemifreeRawDAJoinFamily A)
      (strictSemifreeComputedDAJoinFamily A) := by
  have h := fullFamilyUncurryIso (strictSemifreeComputedFunctorCoconeIso A)
  simpa only [strictSemifreeRawFunctorCoconeMap, strictSemifreeReindexedRawDAJoinFamily,
    uncurry_curry, strictSemifreeComputedDAJoinFamily] using h

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
