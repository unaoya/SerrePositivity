module

public import SerrePositivity.InfinityCategories.F2.Ind.IndConeExtendedCommaFamily
public import SerrePositivity.InfinityCategories.F2.Ind.SmallDiagramComma
public import SerrePositivity.InfinityCategories.Core.UniverseLimits

/-!
概要：元の下方図式の comma が κ-filtered なら、その余錐形状の元の comma も κ-filtered。
方針：指定下方余錐と元の試験族を同時に延長し、同じ小さい模型へ厳密に降ろす。
規約：元の q 自身の実余錐を構成し、ModelCategory 仮定や充填入力を加えない。
使われ方：有限半順序形状の点追加における下方余錐の局所構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) [Fact κ.IsRegular] {L C : SSet.{u}} [Quasicategory C]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj (join L (Δ[0] : SSet.{u})) ⟶ IndInfinity κ C)
/-- 概要：元の試験族と指定下方余錐から、元の全図式 comma の実余錐を構成できる。
方針：全拡張データと厳密な旧族回収。規約：元の q。使われ方：点追加の局所余錐。 -/
lemma nonempty_indConeDiagramComma_cocone_of_lower_cocone
    {A : SSet.{u}} (hA : IsKappaSmall κ A) (hL : IsKappaSmall κ L)
    (q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ diagramComma κ D)
    (G : JoinCocone (q ≫ diagramCommaRestriction κ D (joinInl L (Δ[0] : SSet.{u})))) :
    Nonempty (JoinCocone q) := by
  obtain ⟨V⟩ := indConeExtendedSliceData_nonempty κ D q G hA hL
  exact ⟨indConeExtendedCommaCocone V⟩
/-- 概要：下方の元の comma の κ-filtered 性から、元の余錐図式で実余錐が存在。
方針：小さい下方模型の余錐を同じ大きい comma に移す。規約：全族を保持。使われ方：帰納。 -/
lemma nonempty_indConeDiagramComma_cocone (hL : IsKappaSmall κ L)
    (hLower : IsKappaFiltered κ (smallDiagramComma κ
      ((SSet.uliftFunctor.{u + 1, u}).map (joinInl L (Δ[0] : SSet.{u})) ≫ D)))
    {A : SSet.{u}} (hA : IsKappaSmall κ A)
    (q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ diagramComma κ D) :
    Nonempty (JoinCocone q) := by
  letI := hLower
  obtain ⟨G⟩ := nonempty_cocone_liftedShape_of_equivalence
    (qCatEquivalenceOfIso (smallDiagramCommaIso κ
      ((SSet.uliftFunctor.{u + 1, u}).map (joinInl L (Δ[0] : SSet.{u})) ≫ D))) hA
    (q ≫ diagramCommaRestriction κ D (joinInl L (Δ[0] : SSet.{u})))
  exact nonempty_indConeDiagramComma_cocone_of_lower_cocone κ D hA hL q G
/-- 概要：同じ余錐図式の小さい元の comma は、下方の κ-filtered 性から κ-filtered。
方針：元の任意の小さい全族の実余錐を降下。規約：元の添字。使われ方：有限形状の帰納。 -/
lemma smallConeDiagramComma_isKappaFiltered_of_lower (hL : IsKappaSmall κ L)
    (hLower : IsKappaFiltered κ (smallDiagramComma κ
      ((SSet.uliftFunctor.{u + 1, u}).map (joinInl L (Δ[0] : SSet.{u})) ≫ D))) :
    IsKappaFiltered κ (smallDiagramComma κ D) := by
  constructor
  intro A hA f
  let q := (SSet.uliftFunctor.{u + 1, u}).map f ≫ (smallDiagramCommaIso κ D).hom
  obtain ⟨c⟩ := nonempty_indConeDiagramComma_cocone κ D hL hLower hA q
  have hc : JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map f) := by
    simpa only [q, Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      mapJoinCocone (smallDiagramCommaIso κ D).inv c
  obtain ⟨d, _⟩ := JoinCocone.ulift_surjective.{u, u + 1} f hc
  exact ⟨d⟩
end SerrePositivity.InfinityCategories.F2.Ind
