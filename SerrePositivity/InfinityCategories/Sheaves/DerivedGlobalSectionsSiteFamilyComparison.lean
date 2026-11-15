module

public import SerrePositivity.InfinityCategories.Sheaves.SheafificationSiteComparison
public import SerrePositivity.InfinityCategories.Sheaves.GlobalSectionsSiteFamilyComparison

/-!
概要：site 同値に沿い、任意の前層の全 RΓ 関手を比較する。
方針：同じ指定層化の全関手同型に Γ を後合成し、全 Γ の site 比較につなぐ。
使われ方：BS Remark 4.5、HTT 6.2.2.7、Kerodon §6.1.3（Tag 02D4）。
規約：層である前層だけへ制限しない。全パラメータの射と高次単体を同時に保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
variable {E : SSet.{u + 1}} [Quasicategory E]

/-- 対応する位相を持つ site 同値に沿う、任意の前層の全 RΓ 関手の比較。 -/
def derivedGlobalSectionsReindexFunctorIso (e : C ≌ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (hf : CoverPreserving J K e.functor) (hg : CoverPreserving K J e.inverse)
    (hJ : Sheafification J E) (hK : Sheafification K E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    FunctorIso (reindexPresheafFunctor e.functor ≫ derivedGlobalSectionsFunctor J hJ hE)
      (derivedGlobalSectionsFunctor K hK hE) := by
  let a := (sheafificationReindexFunctorIso e J K hf hg hJ hK).postcomp
    (globalSectionsFunctor hE)
  let b := (globalSectionsReindexFunctorIso e hE).precomp (sheafificationFunctor K hK)
  simpa only [derivedGlobalSectionsFunctor, Category.assoc] using a.symm ≪≫ b

end SerrePositivity.InfinityCategories.Sheaves
