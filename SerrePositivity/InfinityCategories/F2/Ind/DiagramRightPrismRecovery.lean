module

public import SerrePositivity.InfinityCategories.F2.Ind.DiagramRightPrismCurry

/-!
概要：元の C 全族と全円柱を戻すと、元の図式 comma の同じ族を厳密に回収する。
方針：二つの随伴と対称な因子交換の往復を照合し、実引き戻しで比較する。
規約：同型への置換でなく元の全族の等号を示す。
使われ方：再構成した余錐の旧族と指定下方余錐を厳密に回収する。
-/

@[expose] public section
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {K C : SSet.{u}} [Quasicategory C]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ IndInfinity κ C)
  {T : SSet.{u + 1}} (q : T ⟶ diagramComma κ D)
/-- 概要：元の全族は同じ C 全族と全円柱で厳密に決定される。
方針：元の随伴の往復。規約：全射の等号。使われ方：元の指定族の厳密な回収。 -/
lemma diagramRightFamilyCurry_original :
    diagramRightFamilyCurry (diagramCommaOriginalFamily κ D q) =
      q ≫ diagramCommaProjection κ D := by
  rw [diagramRightFamilyCurry, diagramCommaOriginalFamily, ← Category.assoc,
    SymmetricCategory.symmetry, Category.id_comp, curry_uncurry]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
/-- 概要：元の全族は同じ C 全族と全円柱で厳密に決定される。
方針：元の随伴の往復。規約：全射の等号。使われ方：元の指定族の厳密な回収。 -/
lemma diagramRightPrismCurry_original :
    diagramRightPrismCurry κ (diagramCommaRightPrism κ D q) =
      sliceOverUncurry (q ≫ pullback.snd (diagramYoneda κ K C)
        (sliceOverProjection (SSet.yonedaEquiv.symm (functorVertex D)))) := by
  rw [diagramRightPrismCurry, diagramCommaRightPrism, diagramCommaPrism,
    ← Category.assoc, SymmetricCategory.symmetry, Category.id_comp, curry_uncurry]
  exact (sliceOverUncurry_precomp _ q).symm
/-- 概要：元の全族は同じ C 全族と全円柱で厳密に決定される。
方針：元の随伴の往復。規約：全射の等号。使われ方：元の指定族の厳密な回収。 -/
lemma diagramComma_rightFamily_ext {r : T ⟶ diagramComma κ D}
    (hP : diagramCommaOriginalFamily κ D q = diagramCommaOriginalFamily κ D r)
    (hW : diagramCommaRightPrism κ D q = diagramCommaRightPrism κ D r) : q = r := by
  apply pullback.hom_ext
  · have h := congrArg (fun P ↦ diagramRightFamilyCurry P) hP
    simpa only [diagramRightFamilyCurry_original] using h
  · have h := congrArg (fun W ↦ diagramRightPrismCurry κ W) hW
    simp only [diagramRightPrismCurry_original] at h
    calc
      _ = sliceOverCurry (sliceOverUncurry (q ≫ pullback.snd _ _))
          (sliceOverUncurry_fixed _) := (sliceOverCurry_uncurry _).symm
      _ = sliceOverCurry (sliceOverUncurry (r ≫ pullback.snd _ _))
          (sliceOverUncurry_fixed _) := by congr 1
      _ = _ := sliceOverCurry_uncurry _
end SerrePositivity.InfinityCategories.F2.Ind
