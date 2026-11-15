module

public import SerrePositivity.InfinityCategories.Sheaves.SheafSiteInvariance
public import SerrePositivity.InfinityCategories.Sheaves.DerivedGlobalSectionsComparison

/-!
概要：site 同値に沿う同じ指定極限錐から Γ の値を比較する。
方針：元の大域切断錐を同じ形状写像で制限し、極限錐の一意性を使う。
使われ方：HTT 6.2.2.6、Kerodon §7.1（Tag 02K2）の同値な添字での大域切断。
規約：このファイルは値の比較。層化を含む全関手の比較を代用しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
variable {E : SSet.{u + 1}} [Quasicategory E]

/-- 同じ site 写像に沿う極限錐の制限による、元の Γ 頂点の比較。 -/
def globalSectionsReindexIso (e : C ≌ D)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (O : Presheaf D E) :
    VertexIso (globalSections (reindexPresheaf e.functor O) (hasLimit_presheaf hE _))
      (globalSections O (hasLimit_presheaf hE O)) := by
  let c := globalSectionsCone O (hasLimit_presheaf hE O)
  let d := restrictJoinCone c (siteShapeMap e.functor)
  have hd : IsLimitCone d :=
    (isLimitCone_iff_restrict_equivalentShape _ (siteShapeMap_isQCatEquivalence e) c).mp
      (globalSectionsCone_isLimit O _)
  exact limitVertexIso (globalSectionsCone (reindexPresheaf e.functor O) (hasLimit_presheaf hE _))
      d (globalSectionsCone_isLimit _ _) hd ≪≫
    eqToIso (congrArg HomotopyCategory.mk (restrictJoinCone_vertex c (siteShapeMap e.functor)))

/-- 層の場合の RΓ の値の比較は、同じ単位の Γ 比較を通る。 -/
def derivedGlobalSectionsReindexIso_of_isSheaf (e : C ≌ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (hf : CoverPreserving J K e.functor)
    (hJ : Sheafification J E) (hK : Sheafification K E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    {O : Presheaf D E} (hO : IsSheaf K O) :
    VertexIso (derivedGlobalSections J hJ hE (reindexPresheaf e.functor O))
      (derivedGlobalSections K hK hE O) :=
  derivedGlobalSectionsSheafIso J hJ hE (hO.reindex_of_equivalence e hf) ≪≫
    globalSectionsReindexIso e hE O ≪≫ (derivedGlobalSectionsSheafIso K hK hE hO).symm

end SerrePositivity.InfinityCategories.Sheaves
