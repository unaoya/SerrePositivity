module

public import SerrePositivity.InfinityCategories.Sheaves.SheafificationSiteSpecifiedUnit
public import SerrePositivity.InfinityCategories.Sheaves.GlobalSectionsSiteFamilyComparison

/-!
概要：指定単位を保つ層化比較から、任意の前層の全 RΓ の site 比較を作る。
方針：同じ全層化同型へ Γ を後合成し、既存の指定極限錐族の Γ 比較へ接続する。
使われ方：BS Remark 4.5、HTT 6.2.2.7、Kerodon §6.2（Tag 02EH）の反射と大域切断。
規約：前層が層であることは仮定せず、元の単位を保つ同じ比較を使用する。
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

/-- 指定単位を保つ同じ全層化比較を使った、任意の前層の全 RΓ 比較。 -/
def derivedGlobalSectionsReindexSpecifiedFunctorIso (e : C ≌ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (hf : CoverPreserving J K e.functor) (hg : CoverPreserving K J e.inverse)
    (hJ : Sheafification J E) (hK : Sheafification K E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    FunctorIso (reindexPresheafFunctor e.functor ≫ derivedGlobalSectionsFunctor J hJ hE)
      (derivedGlobalSectionsFunctor K hK hE) := by
  let a := (sheafificationReindexSpecifiedFunctorIso e J K hf hg hJ hK).postcomp
    (globalSectionsFunctor hE)
  let b := (globalSectionsReindexFunctorIso e hE).precomp (sheafificationFunctor K hK)
  simpa only [derivedGlobalSectionsFunctor, Category.assoc] using a.symm ≪≫ b

end SerrePositivity.InfinityCategories.Sheaves
