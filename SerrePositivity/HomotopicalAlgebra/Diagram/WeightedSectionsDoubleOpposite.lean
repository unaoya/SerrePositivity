module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedFunctor

/-!
概要：重み付き切断の標準再添字は二重反対圏では同型となり、元の錐比較を保つ。
方針：MathlibのprecompEnrichedHomの射影式と二重反対の厳密な逆を使う。
使われ方：HTT 4.2.4.4、RR02(a)の係数移送。
規約：重みと係数を同時に同じ標準関手で移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.DiagramModel

lemma weightedSections_precomp_π {I J : Type u} [SmallCategory I] [SmallCategory J]
    (W H : I ⥤ SSet.{u}) (P : J ⥤ I) (j : J) :
    Enriched.FunctorCategory.precompEnrichedHom SSet W H P ≫
      weightedSectionsπ (P ⋙ W) (P ⋙ H) j = weightedSectionsπ W H (P.obj j) := by
  dsimp only [Enriched.FunctorCategory.precompEnrichedHom,
    Enriched.FunctorCategory.precompEnrichedHom', weightedSectionsπ]
  rw [end_.lift_π]
  simp only [Iso.refl_inv, Iso.refl_hom, NatTrans.id_app,
    eHomWhiskerRight_id, Category.id_comp, Category.comp_id]
  change _ ≫ 𝟙 _ ≫ eHomWhiskerLeft SSet (W.obj (P.obj j)) (𝟙 (H.obj (P.obj j))) = _
  rw [eHomWhiskerLeft_id, Category.id_comp, Category.comp_id]

/-- 元のendの再添字写像に、二重反対の標準逆を組み合わせる。 -/
def weightedSectionsOpOpIso (I : Type u) [SmallCategory I] (W H : Iᵒᵖᵒᵖ ⥤ SSet.{u}) :
    weightedSections W H ≅ weightedSections (opOp I ⋙ W) (opOp I ⋙ H) where
  hom := Enriched.FunctorCategory.precompEnrichedHom SSet W H (opOp I)
  inv := Enriched.FunctorCategory.precompEnrichedHom SSet
    (opOp I ⋙ W) (opOp I ⋙ H) (unopUnop I)
  hom_inv_id := by
    apply weightedSections_hom_ext
    intro i
    rw [Category.assoc]
    exact (congrArg (fun f => Enriched.FunctorCategory.precompEnrichedHom SSet W H
      (opOp I) ≫ f) (weightedSections_precomp_π (opOp I ⋙ W) (opOp I ⋙ H)
        (unopUnop I) i)).trans
      ((weightedSections_precomp_π W H (opOp I) i.unop.unop).trans
        (Category.id_comp _).symm)
  inv_hom_id := by
    apply weightedSections_hom_ext
    intro i
    rw [Category.assoc]
    exact (congrArg (fun f => Enriched.FunctorCategory.precompEnrichedHom SSet
      (opOp I ⋙ W) (opOp I ⋙ H) (unopUnop I) ≫ f)
        (weightedSections_precomp_π W H (opOp I) i)).trans
      ((weightedSections_precomp_π (opOp I ⋙ W) (opOp I ⋙ H) (unopUnop I)
        (Opposite.op (Opposite.op i))).trans (Category.id_comp _).symm)

/-- 再添字の射影式は、同じ重み付き錐比較を厳密に保存する。 -/
lemma weightedSectionsOpOpIso_cone (I : Type u) [SmallCategory I]
    (W H : Iᵒᵖᵒᵖ ⥤ SSet.{u}) (c : Cone H) :
    weightedConeComparison W c ≫ (weightedSectionsOpOpIso I W H).hom =
      weightedConeComparison (opOp I ⋙ W) (c.whisker (opOp I)) := by
  apply weightedSections_hom_ext
  intro i
  dsimp only [weightedSectionsOpOpIso]
  rw [Category.assoc, weightedSections_precomp_π,
    weightedConeComparison_π, weightedConeComparison_π]
  rfl

end SerrePositivity.DiagramModel
