module

public import SerrePositivity.InfinityCategories.Sheaves.GlobalSectionsFunctor
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveUnitInvertible

/-!
概要：層の全族で、元の反射単位に沿う Γ・RΓ と位相の比較を固定する。
方針：包含への制限で可逆な同じ反射単位を、全 Γ 関手で送る。
  文献対応：HTT 6.2.2.7、Kerodon §6.2（Tag 02EH）、BS Remark 4.5。
規約：全パラメータ上の関手同型を返す。位相の比較にも同じ単位を用いる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]

/-- 層である前層の頂点が張る全部分準圏。 -/
abbrev SheafCat (J : GrothendieckTopology C) (E : SSet.{u + 1}) : SSet.{u + 1} :=
  fullSubcomplexOnVertices (PresheafCat C E) (sheafProperty (E := E) J)

/-- 元の層条件の充満部分圏の包含。 -/
def sheafInclusion (J : GrothendieckTopology C) : SheafCat J E ⟶ PresheafCat C E :=
  (fullSubcomplexOnVertices (PresheafCat C E) (sheafProperty (E := E) J)).ι

/-- 元の反射単位は、任意の層の全族で Γ と RΓ の同型になる。 -/
def sheafGlobalSectionsUnitIso (J : GrothendieckTopology C) (hJ : Sheafification J E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    {A : SSet.{u + 1}} (s : A ⟶ SheafCat J E) :
    FunctorIso ((s ≫ sheafInclusion J) ≫ globalSectionsFunctor hE)
      ((s ≫ sheafInclusion J) ≫ derivedGlobalSectionsFunctor J hJ hE) := by
  simpa only [Category.assoc, derivedGlobalSectionsFunctor, sheafificationFunctor,
    sheafInclusion] using
    (((Classical.choice hJ).unitOnInclusionIso.precomp s).postcomp (globalSectionsFunctor hE))

/-- 細かい位相の層を、粗い位相の層として読む。 -/
def sheafTopologyInclusion (J J' : GrothendieckTopology C) (h : J ≤ J') :
    SheafCat J' E ⟶ SheafCat J E :=
  fullSubcomplexLift (sheafProperty (E := E) J) (sheafInclusion J') (by
    intro x
    have hx := fullSubcomplexOnVertices_vertex x
    exact hx.of_le h)

/-- 層の位相間の包含は、元の前層圏への包含と厳密に整合する。 -/
lemma sheafTopologyInclusion_comp (J J' : GrothendieckTopology C) (h : J ≤ J') :
    sheafTopologyInclusion (E := E) J J' h ≫ sheafInclusion J = sheafInclusion J' :=
  fullSubcomplexLift_ι _ _ _

/-- 位相の比較も、全族で元の単位二つの比較として構成する。 -/
def derivedGlobalSectionsTopologyFamilyIso (J J' : GrothendieckTopology C) (h : J ≤ J')
    (hJ : Sheafification J E) (hJ' : Sheafification J' E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    {A : SSet.{u + 1}} (s : A ⟶ SheafCat J' E) :
    FunctorIso ((s ≫ sheafInclusion J') ≫ derivedGlobalSectionsFunctor J hJ hE)
      ((s ≫ sheafInclusion J') ≫ derivedGlobalSectionsFunctor J' hJ' hE) := by
  have e := sheafGlobalSectionsUnitIso J hJ hE (s ≫ sheafTopologyInclusion J J' h)
  rw [Category.assoc s, sheafTopologyInclusion_comp] at e
  exact e.symm ≪≫ sheafGlobalSectionsUnitIso J' hJ' hE s

end SerrePositivity.InfinityCategories.Sheaves
