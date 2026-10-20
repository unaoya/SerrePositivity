module

public import SerrePositivity.InfinityCategories.F1.QCatDiagramPrism
public import SerrePositivity.InfinityCategories.F1.CoherentQCatInvertible
public import SerrePositivity.InfinityCategories.Core.FunctorEdgePointwise

/-!
概要：対象ごとの同値である自然変換を coherent な Cat∞ 値図式間の同型へ移す。
方針：実際の prism の評価を成分の coherent 辺と照合し、点ごとの可逆性を使う。
規約：同じ自然変換の辺を使い、独立に選んだ各値の同値で代用しない。
使われ方：Cat∞ 値 weighted nerve の strict 図式の復元比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 自然変換の coherent な辺の c での評価は、元の成分の coherent な辺。 -/
lemma qCatDiagramNaturalTransformationEdge_at {C : Type u} [Category.{u} C]
    {F G : C ⥤ QCat.{u}} (η : F ⟶ G) (c : C) :
    (evaluateFunctorAt (Y := CatInfinity.{u}) (ULift.up (nerveVertex c))).app _
      (qCatDiagramNaturalTransformationEdge η).edge =
        (coherentNerveEdge (η.app c)).edge := by
  have hd : ((CategoryTheory.Functor.id (Fin 2)).prod'
      ((CategoryTheory.Functor.const (Fin 2)).obj c)) ⋙ qCatDiagramArrow η =
        ComposableArrows.mk₁ (η.app c) := by
    refine CategoryTheory.Functor.ext (fun i => by fin_cases i <;> rfl) ?_
    intro i j f
    fin_cases i <;> fin_cases j
    all_goals first
    | have hf := leOfHom f
      exact False.elim ((by decide : ¬ (1 : Fin 2) ≤ 0) hf)
    | simp [qCatDiagramArrow, CategoryTheory.Functor.uncurry, ComposableArrows.mk₁]
  change enrichedFunctorOfOrderDiagram
    ((⟨ULift.down, fun _ _ h ↦ h⟩ : ULift.{u} (Fin 2) →o Fin 2).toFunctor ⋙
      (((CategoryTheory.Functor.id (Fin 2)).prod'
        ((CategoryTheory.Functor.const (Fin 2)).obj c)) ⋙ qCatDiagramArrow η)) = _
  rw [hd]
  refine EnrichedFunctor.ext SSet (fun i ↦ ?_) (fun i j ↦ ?_)
  · rcases i with ⟨⟨i⟩⟩
    fin_cases i <;> rfl
  · rcases i with ⟨⟨i⟩⟩
    rcases j with ⟨⟨j⟩⟩
    fin_cases i <;> fin_cases j
    all_goals
      simp only [eqToHom_refl, Category.comp_id]
      apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      intro P
      rfl

/-- 成分ごとに同値な自然変換の同じ coherent な辺は可逆。 -/
lemma qCatDiagramNaturalTransformationEdge_isInvertible {C : Type u} [Category.{u} C]
    {F G : C ⥤ QCat.{u}} (η : F ⟶ G)
    (hη : ∀ c, IsQCatEquivalence (X := (F.obj c).obj) (Y := (G.obj c).obj) (η.app c)) :
    IsInvertibleEdge (qCatDiagramNaturalTransformationEdge η) := by
  apply (isInvertibleEdge_iff_evaluateFunctorAt (qCatDiagramNaturalTransformationEdge η)).mpr
  rintro ⟨s⟩
  obtain ⟨c, rfl⟩ : ∃ c : C, s = nerveVertex c := ⟨s.obj 0, ComposableArrows.ext₀ rfl⟩
  apply (isInvertibleEdge_congr
    (qCatDiagramNaturalTransformationEdge_at η c)).mpr
  exact coherentQCatEdge_isInvertible_of_isQCatEquivalence (hη c)

/-- 対象ごとの同値である元の自然変換を、図式全体の coherent な関手同型にする。 -/
def qCatDiagramFunctorIsoOfPointwise {C : Type u} [Category.{u} C]
    {F G : C ⥤ QCat.{u}} (η : F ⟶ G)
    (hη : ∀ c, IsQCatEquivalence (X := (F.obj c).obj) (Y := (G.obj c).obj) (η.app c)) :
    FunctorIso (qCatDiagramCoherentNerve F) (qCatDiagramCoherentNerve G) := by
  letI : IsIso (SSet.Truncated.HomotopyCategory.homMk
      (qCatDiagramNaturalTransformationEdge η)) :=
    qCatDiagramNaturalTransformationEdge_isInvertible η hη
  exact asIso (SSet.Truncated.HomotopyCategory.homMk
    (qCatDiagramNaturalTransformationEdge η))

end SerrePositivity.InfinityCategories
