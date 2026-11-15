module

public import SerrePositivity.InfinityCategories.Sheaves.SieveSiteComparison
public import SerrePositivity.InfinityCategories.Sheaves.SiteReindex
public import SerrePositivity.InfinityCategories.Sheaves.SieveSectionsCriterion
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeNaturality

/-!
概要：同値な site の引き戻し篩で、元の指定制限錐の極限性を比較する。
方針：篩圏の同値と、nerve・持ち上げ・全錐の後合成の公式を用いる。
使われ方：HTT 6.2.2.6、Kerodon §7.1（Tag 02K2）の site の同値による層条件の移送。
規約：元の指定錐全体を比較し、頂点の同値だけで代用しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
variable {E : SSet.{u + 1}} [Quasicategory E]

/-- site 関手は、引き戻した篩の指定錐を元の篩錐の制限に送る。 -/
lemma sieveSiteFunctor_cone (F : C ⥤ D) {U : C} (S : Sieve (F.obj U)) :
    F.op.mapCone (sieveCone (S.functorPullback F)) =
      (sieveCone S).whisker (sieveSiteFunctor F S).op := rfl

/-- 同じ篩錐の nerve と後合成は site の再添字と整合する。 -/
lemma sieveSiteFunctor_restrictionCone_val (F : C ⥤ D) {U : C}
    (S : Sieve (F.obj U)) (O : Presheaf D E) :
    (restrictJoinCone (restrictionCone O S)
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (sieveSiteFunctor F S).op))).val =
        (restrictionCone (reindexPresheaf F O) (S.functorPullback F)).val := by
  unfold restrictionCone
  rw [uliftNerveCone_whisker_val, ← sieveSiteFunctor_cone]
  change (uliftConeShapeIso _ 0).inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map (nerveCone (F.op.mapCone (sieveCone (S.functorPullback F)))).val ≫ O =
    ((uliftConeShapeIso _ 0).inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map (nerveCone (sieveCone (S.functorPullback F))).val) ≫
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap F.op) ≫ O)
  rw [← nerveCone_mapCone, CategoryTheory.Functor.map_comp, Category.assoc, Category.assoc]

/-- site 同値の下で、引き戻した篩の指定錐の極限性は同値。 -/
lemma isLimit_restrictionCone_site_iff (e : C ≌ D) {U : C}
    (S : Sieve (e.functor.obj U)) (O : Presheaf D E) :
    IsLimitCone (restrictionCone (reindexPresheaf e.functor O) (S.functorPullback e.functor)) ↔
      IsLimitCone (restrictionCone O S) := by
  let j := (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (sieveSiteFunctor e.functor S).op)
  have hj : IsQCatEquivalence j := by
    have h := (nerveQCatEquivalence (sieveSiteEquivalence e S).op).isQCatEquivalence
    exact SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IsQCatEquivalence.ulift.{u, u + 1} h
  have hv := sieveSiteFunctor_restrictionCone_val e.functor S O
  exact (SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isLimitCone_iff_of_cone_val_eq _ _ hv).symm.trans
    (isLimitCone_iff_restrict_equivalentShape j hj (restrictionCone O S)).symm

end SerrePositivity.InfinityCategories.Sheaves
