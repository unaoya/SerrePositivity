module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTotalMapNativeModelComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SmallFunctorIsoPostLiftCancellation

/-!
概要：元の模型比較の両端表示を移し、縮小した全空間比較の単位像を元へ回収する。
方針：実射の等式を明示して指定値を移し、同じ宇宙往復と始域縮小の消去を使う。
規約：模型比較を再選択しない。使われ方：模型三角形と元の単位後の三角形の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})

/-- 元の大きい射を縮小した模型の単位終点は、元の同じ射の大きい単位後合成。 -/
lemma coherentNativeModel_smallMap_unit (f : leftUnstraightening F ⟶ leftUnstraightening G) :
    (smallLeftUnstraighteningIso F).inv ≫ (SSet.uliftFunctor.{u + 1, u}).map
      (coherentDiagramTotalUnit F ≫ coherentTotalVertexMap F G
        (smallLeftUnstraighteningOverMap F G f)) = f ≫ coherentLargeTotalUnit G := by
  rw [coherentTotalVertexMap_unit, Functor.map_comp]
  change (smallLeftUnstraighteningIso F).inv ≫
    ((SSet.uliftFunctor.{u + 1, u}).map (smallSimplicialMap f) ≫
      (SSet.uliftFunctor.{u + 1, u}).map (coherentDiagramTotalUnit G)) = _
  rw [smallSimplicialMap_ulift.{u, u + 1} f]
  change (smallLeftUnstraighteningIso F).inv ≫
    ((smallLeftUnstraighteningIso F).hom ≫ f ≫ (smallLeftUnstraighteningIso G).inv) ≫
      (SSet.uliftFunctor.{u + 1, u}).map (coherentDiagramTotalUnit G) = _
  simp only [coherentLargeTotalUnit, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- 同じ元の実射と指定同型の両端表示変更は、同じ模型比較の指定値を保持する。 -/
lemma coherentTotalMapNativeModelComparison_heq_of_heq
    {a b a' b' : smallLeftUnstraightening F ⟶ smallLeftUnstraightening G}
    (e : FunctorIso a b) (e' : FunctorIso a' b') (ha : a = a') (hb : b = b') (he : HEq e e') :
    HEq (coherentTotalMapNativeModelComparison F G e)
      (coherentTotalMapNativeModelComparison F G e') := by
  subst a' b'
  cases eq_of_heq he
  rfl

/-- 元の全空間比較の縮小を模型へ写すと、同じ元の全空間比較の単位後合成を回収する。 -/
lemma coherentTotalMapNativeModelComparison_smallFunctor_heq_large [Quasicategory B]
    {f g : leftUnstraightening F ⟶ leftUnstraightening G} (e : FunctorIso f g) :
    HEq (coherentTotalMapNativeModelComparison F G (smallUnstraighteningFunctorIso F G e))
      (e.postcomp (coherentLargeTotalUnit G)) := by
  unfold coherentTotalMapNativeModelComparison
  exact (vertexIsoOfEq_heq _ _ _).trans (smallUnstraighteningFunctorIso_post_lift_cancel F G e
    (spaceInfinityObject (coherentDiagramTotalVertex G)).obj (coherentDiagramTotalUnit G))

end SerrePositivity.InfinityCategories.F2
