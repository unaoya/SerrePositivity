module

public import SerrePositivity.InfinityCategories.Sheaves.GlobalSectionsConeComparison
public import SerrePositivity.InfinityCategories.Sheaves.SheafUnitConeTransport

/-!
概要：層の RΓ と Γ、および粗い位相との比較を元の単位から構成する。
方針：同じ単位で輸送した極限錐を、同じ Γ の右随伴で比較する。
  文献対応：HTT 6.2.2.7、Kerodon §7.1（Tag 02H1）、BS Remark 4.5。
規約：位相比較には元の前層が細かい位相の層であることを要求する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]

/-- 層の RΓ は、同じ単位で輸送した元の前層の極限錐の頂点。 -/
theorem derivedGlobalSections_of_isSheaf (J : GrothendieckTopology C)
    (hJ : Sheafification J E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    {F : Presheaf C E} (hF : IsSheaf J F) :
    ∃ c : JoinCone F, IsLimitCone c ∧ c.vertex = derivedGlobalSections J hJ hE F :=
  derivedGlobalSections_isLimitVertex_of_isSheaf J hJ hE hF

/-- 層の単位で輸送した錐と Γ の同じ随伴による比較同型。 -/
def derivedGlobalSectionsSheafIso (J : GrothendieckTopology C) (hJ : Sheafification J E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    {F : Presheaf C E} (hF : IsSheaf J F) :
    VertexIso (derivedGlobalSections J hJ hE F)
      (globalSections F (hasLimit_presheaf hE F)) := by
  let t := sheafUnitLimitConeTransport J hJ hF (derivedGlobalSectionsCone J hJ hE F)
    (derivedGlobalSectionsCone_isLimit J hJ hE F)
  exact eqToIso (congrArg HomotopyCategory.mk t.vertex_eq.symm) ≪≫
    globalSectionsConeValueIso hE t.cone t.isLimit ≪≫
      (globalSectionsConeValueIso hE (globalSectionsCone F (hasLimit_presheaf hE F))
        (globalSectionsCone_isLimit F _)).symm

/-- 両位相の比較を、同じ Γ の頂点を経由する指定同型として固定する。 -/
def derivedGlobalSectionsTopologyIso (J J' : GrothendieckTopology C) (h : J ≤ J')
    (hJ : Sheafification J E) (hJ' : Sheafification J' E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    {F : Presheaf C E} (hF : IsSheaf J' F) :
    VertexIso (derivedGlobalSections J hJ hE F) (derivedGlobalSections J' hJ' hE F) :=
  derivedGlobalSectionsSheafIso J hJ hE (hF.of_le h) ≪≫
    (derivedGlobalSectionsSheafIso J' hJ' hE hF).symm

/-- 粗い位相との比較を実際の可逆な辺で表す。 -/
theorem derivedGlobalSections_of_le (J J' : GrothendieckTopology C) (h : J ≤ J')
    (hJ : Sheafification J E) (hJ' : Sheafification J' E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    {F : Presheaf C E} (hF : IsSheaf J' F) :
    ∃ e : E.Edge (derivedGlobalSections J hJ hE F) (derivedGlobalSections J' hJ' hE F),
      IsInvertibleEdge e.toTruncated := by
  let i := derivedGlobalSectionsTopologyIso J J' h hJ hJ' hE hF
  obtain ⟨e, he⟩ := homotopyCategory_homMk_surjective _ _ i.hom
  refine ⟨⟨e.edge, e.src_eq, e.tgt_eq⟩, ?_⟩
  change IsIso (Truncated.HomotopyCategory.homMk e)
  rw [he]
  infer_instance

end SerrePositivity.InfinityCategories.Sheaves
