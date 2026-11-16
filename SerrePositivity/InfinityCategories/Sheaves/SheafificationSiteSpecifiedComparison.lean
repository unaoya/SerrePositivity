module

public import SerrePositivity.InfinityCategories.Sheaves.SheafificationSiteComparison
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.EquivalenceSquareMate
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.EquivalenceAdjunctionIsoData

/-!
概要：site 同値と層の包含の元の正方形から、指定した可逆な層化比較を作る。
方針：同じ二つの反射の随伴と縦の同値に、既存の二重 mate の全単射を使う。
  文献対応：HTT 6.2.2.7、Kerodon §6.2（Tag 02EH）の単位を保つ全関手の輸送。
規約：元の指定正方形への mate の等式を保持し、hJ・hK を選び直さない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Bicategory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
variable {E : SSet.{u + 1}} [Quasicategory E]

local instance sheafificationSiteSpecifiedHomCategory (A B : SSet.QCat.{u + 1}) :
    Category.{u + 1} (A ⟶ B) := SSet.QCat.bicategory.homCategory A B

/-- 元の層の包含と再添字の厳密な正方形を、同じ全二胞体として固定する。 -/
def sheafInclusionReindexIso (e : C ≌ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (hf : CoverPreserving J K e.functor) :
    FunctorIso (sheafInclusion (E := E) K ≫ reindexPresheafFunctor e.functor)
      (reindexSheafFunctor (E := E) e J K hf ≫ sheafInclusion J) :=
  eqToIso (congrArg (fun f ↦ HomotopyCategory.mk (functorVertex f))
    (reindexSheafFunctor_comp e J K hf).symm)

/-- 元の包含の正方形を mate として保つ、同じ二つの反射の可逆な比較。 -/
def sheafificationReindexSpecifiedMateIso (e : C ≌ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (hf : CoverPreserving J K e.functor) (hg : CoverPreserving K J e.inverse)
    (hJ : Sheafification J E) (hK : Sheafification K E) :
    qcatMap (reindexPresheafFunctor e.functor ≫ (Classical.choice hJ).reflector) ≅
      qcatMap ((Classical.choice hK).reflector ≫ reindexSheafFunctor e J K hf) := by
  let t := (reindexPresheafFunctor_isQCatEquivalence (E := E) e).choose
  let s := (reindexSheafFunctor_isQCatEquivalence (E := E) e J K hf hg).choose
  haveI : IsIso (equivalenceAdjunction t).unit := equivalenceAdjunction_unit_isIso t
  haveI : IsIso (equivalenceAdjunction s).counit := equivalenceAdjunction_counit_isIso s
  exact equivalenceSquareMateIso (Classical.choice hK).adjunction (Classical.choice hJ).adjunction
    (equivalenceAdjunction t) (equivalenceAdjunction s)
    (functorIsoToQcatIso (sheafInclusionReindexIso e J K hf))

/-- 同じ比較の mate は、元の層の包含の指定全二胞体そのものである。 -/
lemma sheafificationReindexSpecifiedMateIso_mate (e : C ≌ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (hf : CoverPreserving J K e.functor) (hg : CoverPreserving K J e.inverse)
    (hJ : Sheafification J E) (hK : Sheafification K E) :
    mateEquiv (Classical.choice hK).adjunction (Classical.choice hJ).adjunction
      (sheafificationReindexSpecifiedMateIso e J K hf hg hJ hK).hom =
        (functorIsoToQcatIso (sheafInclusionReindexIso (E := E) e J K hf)).hom := by
  let t := (reindexPresheafFunctor_isQCatEquivalence (E := E) e).choose
  let s := (reindexSheafFunctor_isQCatEquivalence (E := E) e J K hf hg).choose
  haveI : IsIso (equivalenceAdjunction t).unit := equivalenceAdjunction_unit_isIso t
  haveI : IsIso (equivalenceAdjunction s).counit := equivalenceAdjunction_counit_isIso s
  exact equivalenceSquareMateIso_mate (Classical.choice hK).adjunction
    (Classical.choice hJ).adjunction (equivalenceAdjunction t) (equivalenceAdjunction s)
    (functorIsoToQcatIso (sheafInclusionReindexIso e J K hf))

/-- 指定した包含の正方形と同じ横の mate による、全前層上の層化比較。 -/
def sheafificationReindexSpecifiedFunctorIso (e : C ≌ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (hf : CoverPreserving J K e.functor) (hg : CoverPreserving K J e.inverse)
    (hJ : Sheafification J E) (hK : Sheafification K E) :
    FunctorIso (sheafificationFunctor K hK ≫ reindexPresheafFunctor e.functor)
      (reindexPresheafFunctor e.functor ≫ sheafificationFunctor J hJ) := by
  let α := qcatIsoToFunctorIso (sheafificationReindexSpecifiedMateIso e J K hf hg hJ hK)
  let h := (sheafInclusionReindexIso (E := E) e J K hf).precomp (Classical.choice hK).reflector
  change FunctorIso (((Classical.choice hK).reflector ≫ sheafInclusion K) ≫
      reindexPresheafFunctor e.functor)
    (reindexPresheafFunctor e.functor ≫ ((Classical.choice hJ).reflector ≫ sheafInclusion J))
  simpa only [Category.assoc] using h ≪≫ (α.postcomp (sheafInclusion J)).symm

end SerrePositivity.InfinityCategories.Sheaves
