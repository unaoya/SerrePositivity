module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowInterpolationOldFamilyIso
public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowInterpolationExistence
public import SerrePositivity.InfinityCategories.F2.Ind.SmallDiagramComma
public import SerrePositivity.InfinityCategories.F2.CoconeExistenceTransport
public import SerrePositivity.InfinityCategories.Stable.UniverseLimits

/-!
概要：元の任意の射図式の実 diagram comma の小さい模型は κ-filtered。
方針：実補間族の全余錐を元の q へ輸送し、小さい実模型へ厳密に降ろす。
規約：元の全変換族・指定図式を保持。使われ方：射の単一 filtered 表示と安定性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 同じ元の補間全族自体が、その元の制限族への実全余錐を与える。 -/
def indArrowInterpolationOldFamilyCocone
    {κ : Cardinal.{u}} {C A : SSet.{u}} [Quasicategory C]
    {D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C}
    {q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ diagramComma κ D}
    (V : IndArrowInterpolationData κ D q) : JoinCocone (indArrowInterpolationOldFamily V) :=
  ⟨(uliftCoconeShapeIso.{u, u + 1} A 0).inv ≫ indArrowInterpolationCommaFamily V, by
    rw [← Category.assoc, uliftCoconeShapeIso_inv_inl]
    rfl⟩

variable (κ : Cardinal.{u}) [Fact κ.IsRegular] {C : SSet.{u}} [Quasicategory C]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C)

/-- 元の任意の κ-small な全試験族 q は、同じ実射図式 comma 内で全余錐を持つ。 -/
lemma nonempty_indArrowDiagramComma_cocone {A : SSet.{u}} (hA : IsKappaSmall κ A)
    (q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ diagramComma κ D) :
    Nonempty (JoinCocone q) := by
  obtain ⟨V⟩ := indArrowInterpolationData_nonempty κ D hA q
  obtain ⟨e⟩ := nonempty_indArrowInterpolationOldFamily_iso V
  exact nonempty_joinCocone_of_functorIso e ⟨indArrowInterpolationOldFamilyCocone V⟩

/-- 同じ元の射図式を表示する小さい実 comma 模型は、追加仮定なしに κ-filtered。 -/
lemma smallArrowDiagramComma_isKappaFiltered : IsKappaFiltered κ (smallDiagramComma κ D) := by
  constructor
  intro A hA f
  let q := (SSet.uliftFunctor.{u + 1, u}).map f ≫ (smallDiagramCommaIso κ D).hom
  obtain ⟨c⟩ := nonempty_indArrowDiagramComma_cocone κ D hA q
  have hc : JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map f) := by
    simpa only [q, Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      mapJoinCocone (smallDiagramCommaIso κ D).inv c
  obtain ⟨d, _⟩ := JoinCocone.ulift_surjective.{u, u + 1} f hc
  exact ⟨d⟩

end SerrePositivity.InfinityCategories.F2.Ind
