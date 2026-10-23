module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeNativeEnriched
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeAssociativityEnriched
public import SerrePositivity.InfinityCategories.F1.Categories.QuasicategoryEnrichedDiagramRestriction

/-!
概要：指定結合同型の全局所比較を元の全 fibration へ制限した終域は、直接底変換の作用。
方針：同じ section 結合同型の自然性を比較し、同型による前合成を消去する。
規約：元の全相対 Hom と元の section 結合同型の値を保持する。
使われ方：元の大域結合比較の族と全局所比較の族を厳密に同定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- 全局所の section 比較を元の二重底変換で前合成する。 -/
def cocartesianBaseChangeNativeSectionComparison
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (a : A) :
    QuasicategoryEnrichedComparison
      (((cocartesianFibrationBaseChangeEnriched (nerveMap k)).comp SSet
        (cocartesianFibrationBaseChangeEnriched (nerveMap l))).comp SSet
          (cocartesianSectionsEnrichedEvaluation (Over.mk (nerveMap (Under.forget a)))))
      ((cocartesianBaseChangeNativeEnriched l k).comp SSet
        ((isoTransportTargetEnriched SSet.{u} (CocartesianFibrationObject (nerve A))).comp SSet
          (cocartesianSectionsEnrichedEvaluation (Over.mk (nerveMap (Under.forget a)))))) :=
  (cocartesianIsoTransportSectionComparison (Over.mk (nerveMap (Under.forget a)))).precompose
    (cocartesianBaseChangeNativeEnriched l k)

/-- 同じ前合成された比較の成分は、既存の section 結合同型そのもの。 -/
lemma cocartesianBaseChangeNativeSectionComparison_component
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (a : A) (p : CocartesianFibrationObject (nerve C)) :
    (cocartesianBaseChangeNativeSectionComparison l k a).val p =
      (cocartesianBaseChangeAssociativityComponent p.val.hom l k a).hom :=
  cocartesianIsoTransportSectionComparison_native_component l k p a

/-- 元の全相対 Hom 上で、指定同型の終域評価は直接底変換後の section 評価そのもの。 -/
lemma cocartesianBaseChangeNativeEnriched_sectionTarget
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (a : A) :
    (cocartesianBaseChangeNativeEnriched l k).comp SSet
      ((isoTransportTargetEnriched SSet.{u} (CocartesianFibrationObject (nerve A))).comp SSet
        (cocartesianSectionsEnrichedEvaluation (Over.mk (nerveMap (Under.forget a))))) =
    (cocartesianFibrationBaseChangeEnriched (nerveMap (l ⋙ k))).comp SSet
      (cocartesianSectionsEnrichedEvaluation (Over.mk (nerveMap (Under.forget a)))) := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro p q
  simp only [eqToHom_refl, Category.comp_id]
  apply uncurry_injective
  apply (cancel_epi ((cocartesianBaseChangeAssociativityComponent p.val.hom l k a).hom ▷
    SimplicialCategory.sHom p q)).mp
  have h := (cocartesianBaseChangeNativeSectionComparison l k a).property p q
  rw [cocartesianBaseChangeNativeSectionComparison_component,
    cocartesianBaseChangeNativeSectionComparison_component] at h
  exact h.trans ((cocartesianBaseChangeAssociativityEnrichedComparison l k a).property p q).symm

end SerrePositivity.InfinityCategories
