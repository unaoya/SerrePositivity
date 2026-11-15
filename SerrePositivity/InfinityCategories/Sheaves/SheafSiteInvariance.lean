module

public import SerrePositivity.InfinityCategories.Sheaves.SieveSiteConeComparison
public import SerrePositivity.InfinityCategories.Sheaves.SheafEquivalence
public import Mathlib.CategoryTheory.Sites.Equivalence

/-!
概要：対応する被覆位相を持つ site 同値に沿い、層条件を保存し反映する。
方針：元の篩圏の同値と指定錐比較を用い、逆向きは同じ site 同値の余単位で戻す。
使われ方：HTT 6.2.2.6、Kerodon §4.5.1（Tag 01DQ）の site の同値による輸送。
規約：元の被覆保存性を両向きに明示し、小さい模型以外の新しい濃度条件を加えない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
variable {E : SSet.{u + 1}} [Quasicategory E]

/-- 同値の余単位は全前層の二重再添字を元へ戻す同じ全同型を与える。 -/
def reindexPresheaf_inverseFunctorIso (e : C ≌ D) (O : Presheaf D E) :
    FunctorIso (reindexPresheaf e.inverse (reindexPresheaf e.functor O)) O := by
  let h := ((nerveQCatEquivalence e.op).invHomIso).ulift.{u, u + 1}
  change FunctorIso
    ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap e.inverse.op ≫ nerveMap e.functor.op))
    ((SSet.uliftFunctor.{u + 1, u}).map (𝟙 (nerve Dᵒᵖ))) at h
  simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.assoc, siteShapeMap, reindexPresheaf] using h.postcomp O

/-- 被覆を保つ site 同値に沿う再添字は元の層条件を保つ。 -/
lemma IsSheaf.reindex_of_equivalence (e : C ≌ D)
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (hcov : CoverPreserving J K e.functor) {O : Presheaf D E} (hO : IsSheaf K O) :
    IsSheaf J (reindexPresheaf e.functor O) := by
  intro U S hS
  have h := (isLimit_restrictionCone_site_iff e (S.functorPushforward e.functor) O).mpr
    (hO _ _ (hcov.cover_preserve hS))
  have he : (S.functorPushforward e.functor).functorPullback e.functor = S :=
    Sieve.functorPullback_functorPushforward_eq e.functor
  rw [he] at h
  exact h

/-- 両向きの元の被覆保存性を持つ site 同値では、層条件が同値。 -/
theorem isSheaf_reindex_equivalence_iff (e : C ≌ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (hf : CoverPreserving J K e.functor) (hg : CoverPreserving K J e.inverse)
    (O : Presheaf D E) : IsSheaf J (reindexPresheaf e.functor O) ↔ IsSheaf K O := by
  constructor
  · intro h
    exact (h.reindex_of_equivalence e.symm hg).of_functorIso
      (reindexPresheaf_inverseFunctorIso e O)
  · exact fun h ↦ h.reindex_of_equivalence e hf

/-- Mathlib の同値に沿う元の誘導位相に特殊化した層条件の輸送。 -/
theorem isSheaf_inducedTopology_equivalence_iff (e : C ≌ D)
    (J : GrothendieckTopology C) (O : Presheaf D E) :
    IsSheaf J (reindexPresheaf e.functor O) ↔
      IsSheaf (e.inverse.inducedTopology J) O := by
  apply isSheaf_reindex_equivalence_iff e J (e.inverse.inducedTopology J)
  · exact CoverPreserving.of_isContinuous (F := e.functor) J (e.inverse.inducedTopology J)
  · exact CoverPreserving.of_isContinuous (F := e.inverse) (e.inverse.inducedTopology J) J

end SerrePositivity.InfinityCategories.Sheaves
