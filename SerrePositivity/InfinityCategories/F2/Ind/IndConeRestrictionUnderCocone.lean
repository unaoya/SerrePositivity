module

public import SerrePositivity.InfinityCategories.F2.Ind.IndConeExtendedCommaLower
public import SerrePositivity.InfinityCategories.F2.Ind.RelativeCommaCoconeLifts
public import SerrePositivity.InfinityCategories.F2.Ind.SmallDiagramComma

/-!
概要：元の余錐図式族と下方図式への指定変換を、同じ実 under comma で延長する。
方針：下方 comma の小さい filtered 模型と、指定全余錐の厳密な持ち上げを使う。
規約：元の q と指定変換を保持し、追加の充填仮定を要求しない。
使われ方：下方制限の共終性と有限半順序図式の旧頂点評価の共終性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：元の余錐図式族と下方への指定全変換を同時に延長する実余錐が存在。
方針：指定下方全余錐を固定して持ち上げる。規約：元の全族。使われ方：下方制限の共終性。 -/
lemma nonempty_indConeRestrictionUnder_cocone (κ : Cardinal.{u}) [Fact κ.IsRegular]
    {K C : SSet.{u}} [Quasicategory C]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (join K (Δ[0] : SSet.{u})) ⟶ IndInfinity κ C)
    (hK : IsKappaSmall κ K)
    (hLower : IsKappaFiltered κ (smallDiagramComma κ
      ((SSet.uliftFunctor.{u + 1, u}).map (joinInl K (Δ[0] : SSet.{u})) ≫ D)))
    {A B : SSet.{u}} (hA : IsKappaSmall κ A) (hB : IsKappaSmall κ B)
    (z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ diagramComma κ
      ((SSet.uliftFunctor.{u + 1, u}).map (joinInl K (Δ[0] : SSet.{u})) ≫ D))
    (q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ diagramComma κ D)
    (t : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ sliceUnder z)
    (ht : q ≫ diagramCommaRestriction κ D (joinInl K (Δ[0] : SSet.{u})) =
      t ≫ sliceUnderProjection z) :
    Nonempty (JoinCocone (relativeCommaFamily
      (diagramCommaRestriction κ D (joinInl K (Δ[0] : SSet.{u}))) z t q ht)) := by
  letI := hLower
  apply nonempty_relativeComma_cocone_of_cocone_lifts
    (diagramCommaRestriction κ D (joinInl K (Δ[0] : SSet.{u}))) ?_ ?_ hA hB z q t ht
  · intro B hB p
    exact nonempty_cocone_liftedShape_of_equivalence
      (qCatEquivalenceOfIso (smallDiagramCommaIso κ
        ((SSet.uliftFunctor.{u + 1, u}).map (joinInl K (Δ[0] : SSet.{u})) ≫ D))) hB p
  · intro B hB p G
    exact exists_indConeDiagramComma_cocone_fixing_lower p G hB hK
/-- 概要：元の下方制限の実 under 引き戻しで、任意の小さい全族が実余錐を持つ。
方針：二射影の全族を元の族へ厳密に戻す。規約：全射を保持。使われ方：Quillen A の入力。 -/
lemma nonempty_indConeRestrictionComma_cocone (κ : Cardinal.{u}) [Fact κ.IsRegular]
    {K C : SSet.{u}} [Quasicategory C]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (join K (Δ[0] : SSet.{u})) ⟶ IndInfinity κ C)
    (hK : IsKappaSmall κ K)
    (hLower : IsKappaFiltered κ (smallDiagramComma κ
      ((SSet.uliftFunctor.{u + 1, u}).map (joinInl K (Δ[0] : SSet.{u})) ≫ D)))
    {A B : SSet.{u}} (hA : IsKappaSmall κ A) (hB : IsKappaSmall κ B)
    (z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ diagramComma κ
      ((SSet.uliftFunctor.{u + 1, u}).map (joinInl K (Δ[0] : SSet.{u})) ≫ D))
    (q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ pullback (sliceUnderProjection z)
      (diagramCommaRestriction κ D (joinInl K (Δ[0] : SSet.{u})))) :
    Nonempty (JoinCocone q) := by
  let F := diagramCommaRestriction κ D (joinInl K (Δ[0] : SSet.{u}))
  have h : (q ≫ pullback.snd (sliceUnderProjection z) F) ≫ F =
      (q ≫ pullback.fst (sliceUnderProjection z) F) ≫ sliceUnderProjection z := by
    rw [Category.assoc, Category.assoc, pullback.condition]
  have hc := nonempty_indConeRestrictionUnder_cocone κ D hK hLower hA hB z
    (q ≫ pullback.snd (sliceUnderProjection z) F)
    (q ≫ pullback.fst (sliceUnderProjection z) F) h
  have hq : relativeCommaFamily F z (q ≫ pullback.fst (sliceUnderProjection z) F)
      (q ≫ pullback.snd (sliceUnderProjection z) F) h = q := by
    apply pullback.hom_ext <;> simp only [relativeCommaFamily, pullback.lift_fst,
      pullback.lift_snd]
  exact hq ▸ hc
end SerrePositivity.InfinityCategories.F2.Ind
