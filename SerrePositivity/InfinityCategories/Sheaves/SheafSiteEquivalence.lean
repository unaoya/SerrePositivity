module

public import SerrePositivity.InfinityCategories.Sheaves.SheafSiteInvariance
public import SerrePositivity.InfinityCategories.Sheaves.SheafGlobalSectionsFamily
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FunctorVertexConeReindex
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FullSubcomplexRestrictionEquivalence

/-!
概要：対応する被覆位相を持つ site 同値から、層の全部分準圏の同値を作る。
方針：元の再添字の全単体を層の頂点条件へ制限し、既存の全部分圏の同値判定を使う。
  文献対応：HTT 6.2.2.6、Kerodon §4.5.1（Tag 01DQ）の site 同値に沿う層の輸送。
規約：対象だけでなく、元の全前層関手との可換性を等式として保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Project.FilteredExchange
open SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
variable {E : SSet.{u + 1}} [Quasicategory E]

/-- 再添字した頂点から読み戻す前層は、元の前層の再添字と等しい。 -/
lemma vertexToPresheaf_reindex (f : C ⥤ D) (v : (PresheafCat D E) _⦋0⦌) :
    vertexToPresheaf ((reindexPresheafFunctor (E := E) f).app _ v) =
      reindexPresheaf f (vertexToPresheaf v) :=
  functorVertexMap_precomp (siteShapeMap f) v

/-- 元の全再添字関手の頂点では、両向きの被覆保存性が層条件を保存し反映する。 -/
lemma sheafProperty_reindex_equivalence_iff (e : C ≌ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (hf : CoverPreserving J K e.functor) (hg : CoverPreserving K J e.inverse)
    (v : (PresheafCat D E) _⦋0⦌) :
    sheafProperty J ((reindexPresheafFunctor (E := E) e.functor).app _ v) ↔
      sheafProperty K v := by
  dsimp only [sheafProperty]
  rw [vertexToPresheaf_reindex]
  exact isSheaf_reindex_equivalence_iff e J K hf hg _

/-- 被覆を保つ同値による、元の層の頂点条件の移送。 -/
lemma sheafProperty_reindex_of_equivalence (e : C ≌ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (hf : CoverPreserving J K e.functor) (v : (PresheafCat D E) _⦋0⦌)
    (hv : sheafProperty K v) :
    sheafProperty J ((reindexPresheafFunctor (E := E) e.functor).app _ v) := by
  dsimp only [sheafProperty] at hv ⊢
  rw [vertexToPresheaf_reindex]
  exact hv.reindex_of_equivalence e hf

/-- 被覆を保つ site 同値に沿う元の全再添字を、層の全部分準圏へ制限する。 -/
def reindexSheafFunctor (e : C ≌ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (hf : CoverPreserving J K e.functor) : SheafCat K E ⟶ SheafCat J E :=
  fullSubcomplexLift (sheafProperty (E := E) J)
    (sheafInclusion (E := E) K ≫ reindexPresheafFunctor (E := E) e.functor)
    (fun x ↦ sheafProperty_reindex_of_equivalence e J K hf x.val
      (fullSubcomplexOnVertices_vertex x))

/-- 元の全前層関手への包含と、層への制限は厳密に可換する。 -/
lemma reindexSheafFunctor_comp (e : C ≌ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (hf : CoverPreserving J K e.functor) :
    reindexSheafFunctor (E := E) e J K hf ≫ sheafInclusion J =
      sheafInclusion K ≫ reindexPresheafFunctor e.functor :=
  fullSubcomplexLift_ι _ _ _

/-- 対応する被覆位相を持つ site 同値は、層の元の全部分準圏の同値を与える。 -/
theorem reindexSheafFunctor_isQCatEquivalence (e : C ≌ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (hf : CoverPreserving J K e.functor) (hg : CoverPreserving K J e.inverse) :
    IsQCatEquivalence (reindexSheafFunctor (E := E) e J K hf) := by
  apply isQCatEquivalence_fullSubcomplexRestriction
    (sheafProperty (E := E) K) (sheafProperty (E := E) J)
    (fun h ↦ sheafProperty_iff_of_vertexIso J h)
    (reindexPresheafFunctor e.functor) (reindexPresheafFunctor_isQCatEquivalence e)
    _ (reindexSheafFunctor_comp e J K hf)
  intro x hx
  exact (sheafProperty_reindex_equivalence_iff e J K hf hg x).mp hx

end SerrePositivity.InfinityCategories.Sheaves
