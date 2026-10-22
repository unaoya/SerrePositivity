module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ArrowCompositionIso

/-! 対角引き戻しへの逆写像は、元の任意のパラメーター族と二つの射影を保持する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
variable {X T : SSet.{u}} {a b c d : X _⦋0⦌} (f : X.Edge a b) (g : X.Edge c d)
  (h : T ⟶ intervalMappingSpace (functorVertex (SSet.yonedaEquiv.symm f.edge))
    (functorVertex (SSet.yonedaEquiv.symm g.edge)))

lemma dgGluingArrowHomToComposition_precomp :
    h ≫ dgGluingArrowHomToComposition f g = dgGluingArrowHomToCompositionFamily f g h := by
  apply (cancel_mono (dgGluingArrowCompositionPullbackToHom f g)).1
  rw [Category.assoc, dgGluingArrowHomToComposition_toHom, Category.comp_id,
    dgGluingArrowHomToCompositionFamily_comp]

lemma dgGluingArrowCompositionIso_inv_first :
    h ≫ (dgGluingArrowCompositionIso f g).inv ≫ pullback.fst _ _ =
      dgGluingArrowHomFirstComposition f g h := by
  change h ≫ dgGluingArrowHomToComposition f g ≫ _ = _
  rw [← Category.assoc, dgGluingArrowHomToComposition_precomp,
    dgGluingArrowHomToCompositionFamily_first]

lemma dgGluingArrowCompositionIso_inv_last :
    h ≫ (dgGluingArrowCompositionIso f g).inv ≫ pullback.snd _ _ =
      dgGluingArrowHomLastComposition f g h := by
  change h ≫ dgGluingArrowHomToComposition f g ≫ _ = _
  rw [← Category.assoc, dgGluingArrowHomToComposition_precomp,
    dgGluingArrowHomToCompositionFamily_last]

end SerrePositivity.InfinityCategories
