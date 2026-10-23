module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentCoconeTransport
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentNervePost
public import SerrePositivity.InfinityCategories.F1.Simplicial.SimplicialEnrichedOpposite
public import SerrePositivity.InfinityCategories.F1.Coherent.OrderPostcomposition

/-!
概要：反対の coherent nerve からの標準帰還と、同じ豊穣関手による後合成の可換性。
方針：既存の反対比較の自然性を逆向きへ移し、二重反転の自然性で元へ戻す。
規約：局所 Kan 性やモデル圏の仮定を追加しない。
使われ方：元の通常の余錐全体の coherent な後合成の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
open HomotopyLimits
variable {C D : Type v} [Category.{u} C] [Category.{u} D]
  [SimplicialCategory C] [SimplicialCategory D]

/-- 反対豊穣関手の通常の作用は、元の通常の作用の反対そのもの。 -/
lemma coherentUnderlying_opposite (R : EnrichedFunctor SSet.{u} C D) :
    coherentEnrichedUnderlyingFunctor (simplicialEnrichedOpposite R) =
      (coherentEnrichedUnderlyingFunctor R).op := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- 反対の coherent nerve から元へ戻す標準写像は、豊穣関手による後合成と可換。 -/
lemma coherentReturn_postcomp (R : EnrichedFunctor SSet.{u} C D) :
    SSet.opFunctor.map (coherentNerveMap (simplicialEnrichedOpposite R)) ≫
      (coherentOppositeReturnIso D).hom =
        (coherentOppositeReturnIso C).hom ≫ coherentNerveMap R := by
  let eC := coherentNerveOppositeIso C
  let eD := coherentNerveOppositeIso D
  have hn : SSet.opFunctor.map (coherentNerveMap R) ≫ eD.hom =
      eC.hom ≫ coherentNerveMap (simplicialEnrichedOpposite R) :=
    coherentNerveOppositeMap_post R
  have hi : coherentNerveMap (simplicialEnrichedOpposite R) ≫ eD.inv =
      eC.inv ≫ SSet.opFunctor.map (coherentNerveMap R) := by
    rw [← cancel_epi eC.hom, ← Category.assoc, ← hn]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  change SSet.opFunctor.map (coherentNerveMap (simplicialEnrichedOpposite R)) ≫
    (SSet.opFunctor.map eD.inv ≫ _) = (SSet.opFunctor.map eC.inv ≫ _) ≫ _
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, hi,
    CategoryTheory.Functor.map_comp, Category.assoc]
  have hnat : SSet.opFunctor.map (SSet.opFunctor.map (coherentNerveMap R)) ≫
      (SSet.opFunctorCompOpFunctorIso.app (SimplicialNerve D)).hom =
        (SSet.opFunctorCompOpFunctorIso.app (SimplicialNerve C)).hom ≫ coherentNerveMap R :=
    SSet.opFunctorCompOpFunctorIso.hom.naturality (coherentNerveMap R)
  rw [hnat, Category.assoc]

end SerrePositivity.InfinityCategories.F2.Ind
