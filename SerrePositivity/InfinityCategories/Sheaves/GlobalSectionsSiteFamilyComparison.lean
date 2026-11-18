module

public import SerrePositivity.InfinityCategories.Sheaves.GlobalSectionsFamilyData
public import SerrePositivity.InfinityCategories.Sheaves.SiteReindex
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.EquivalentShapeConeFamilies

/-!
概要：site 同値に沿う大域切断の比較を、全前層圏上の一つの関手同型として構成する。
方針：同じ極限錐族を再添字し、S2 の二つの全錐比較を合成する。
  文献対応：HTT 5.4.7.9、Kerodon §7.1（Tag 02K2）の全 Γ 比較。
規約：個々の頂点の同型で、元の射・全高次単体の比較を代用しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Project.FilteredExchange
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
variable {E : SSet.{u + 1}} [Quasicategory E]

/-- 同じ全錐族から得た site 同値と Γ の全関手比較。 -/
def globalSectionsReindexFunctorIso (e : C ≌ D)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    FunctorIso (reindexPresheafFunctor e.functor ≫ globalSectionsFunctor hE)
      (globalSectionsFunctor (C := D) hE) := by
  let s := (globalSectionsFamilyData (C := D) hE).val
  let f := siteShapeMap e.functor
  let t := s ≫ (pre (joinMap (𝟙 (Δ[0] : SSet.{u + 1})) f)).app E
  have hs : s ≫ coneRestriction (presheafShape D) E = 𝟙 _ :=
    globalSectionsFamilyData_restrict hE
  have ht (v : (PresheafCat D E) _⦋0⦌) :
      IsLimitCone (functorVertexCone (t.app _ v)) :=
    (isLimitCone_functorVertexCone_reindex_iff_of_equivalence f
      (siteShapeMap_isQCatEquivalence e) (s.app _ v)).mpr (globalSectionsFamilyData_isLimit hE v)
  have ha : t ≫ evaluateFunctorAt (Y := E)
      (SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u + 1}) (presheafShape C))) =
      s ≫ evaluateFunctorAt (Y := E)
        (SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u + 1}) (presheafShape D))) := by
    dsimp only [t]
    rw [Category.assoc, coneReindex_precomp_apex]
  have hr : t ≫ coneRestriction (presheafShape C) E = reindexPresheafFunctor e.functor := by
    dsimp only [t, reindexPresheafFunctor]
    rw [Category.assoc, coneReindex_precomp_restriction, ← Category.assoc, hs, Category.id_comp]
  let a := globalSectionsConeFamilyIso hE t ht
  let b := globalSectionsConeFamilyIso hE s (globalSectionsFamilyData_isLimit hE)
  rw [ha, hr] at a
  rw [hs, Category.id_comp] at b
  exact a.symm ≪≫ b

end SerrePositivity.InfinityCategories.Sheaves
