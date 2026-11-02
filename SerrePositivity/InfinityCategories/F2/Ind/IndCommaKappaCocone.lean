module

public import SerrePositivity.InfinityCategories.F2.Ind.LiftedShapeCocone
public import SerrePositivity.InfinityCategories.F2.Ind.IndElementsLeftKanModel
public import SerrePositivity.InfinityCategories.Stable.Filtered.KappaFilteredCoslices
public import SerrePositivity.InfinityCategories.F1.ColimitRestriction

/-!
概要：元の Ind 頂点への実 comma とその指定図式の下で小さい余錐を作る。
方針：元の κ-filtered 元の圏との全比較を使い、join の宇宙同型で固定条件を戻す。
規約：指定元の全図式を保持。使われ方：有限半順序図式の頂点追加の局所延長。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) [Fact κ.IsRegular] {C : SSet.{u}} [Quasicategory C]
  (x : (IndInfinity κ C) _⦋0⦌)

/-- 実際の元の Ind comma 上の κ-small な全試験図式は余錐を持つ。 -/
lemma nonempty_indComma_cocone {A : SSet.{u}} (hA : IsKappaSmall κ A)
    (q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ leftKanShape (indYoneda κ C) x) :
    Nonempty (JoinCocone q) := by
  have := indVertexElements_isKappaFiltered κ x
  exact nonempty_cocone_liftedShape_of_equivalence
    (indElementsLeftKanComparison_isQCatEquivalence κ x).choose hA q

/-- 指定 κ-small 図式を保つ元の comma の coslice でも全試験図式に余錐が存在。 -/
lemma nonempty_indComma_coslice_cocone {A L : SSet.{u}}
    (hA : IsKappaSmall κ A) (hL : IsKappaSmall κ L)
    (p : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ leftKanShape (indYoneda κ C) x)
    (q : (SSet.uliftFunctor.{u + 1, u}).obj L ⟶ sliceUnder p) :
    Nonempty (JoinCocone q) := by
  have hjoin := isKappaSmall_join (Fact.out : κ.IsRegular) hA hL
  let e := uliftJoinIso.{u, u + 1} A L
  obtain ⟨c⟩ := nonempty_indComma_cocone κ x hjoin (e.hom ≫ sliceUnderUncurry q)
  have he : e.inv ≫ (e.hom ≫ sliceUnderUncurry q) = sliceUnderUncurry q :=
    e.inv_hom_id_assoc _
  have hc : Nonempty (JoinCocone (sliceUnderUncurry q)) :=
    ⟨he ▸ c.restrict e.inv⟩
  obtain ⟨d⟩ := hc
  exact ⟨diagramNestedCosliceDiagramCurry q Δ[0] d⟩

end SerrePositivity.InfinityCategories.F2.Ind
