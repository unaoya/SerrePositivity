module

public import SerrePositivity.InfinityCategories.Sheaves.DerivedGlobalSections
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallLimitFunctorContinuity

/-!
概要：大域切断と層化後の大域切断の全関手を、同じ反射の単位とともに固定する。
方針：定値図式の右随伴を一度選び、元の反射単位を後合成で送る。
使われ方：HTT 5.5.2.9・6.2.2.7、Kerodon §7.1（Tag 02H1）。
規約：頂点ごとの選択を射への作用の代わりにしない。指定極限錐の頂点との比較は別途保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]

/-- 定値図式の右随伴は presentable 係数から存在する。 -/
lemma exists_globalSectionsFunctor
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    ∃ R : PresheafCat C E ⟶ E,
      Nonempty (QCatAdjunction (constantFunctorMap (presheafShape C) E) R) :=
  (exists_rightAdjoint_iff_preservesSmallColimits hE
    (functor_isPresentable (nerve Cᵒᵖ) hE) _).mpr
      (constantFunctorMap_preservesSmallColimits _)

/-- 全パラメータに同じ右随伴を使う大域切断関手。 -/
def globalSectionsFunctor
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    PresheafCat C E ⟶ E :=
  Classical.choose (exists_globalSectionsFunctor (C := C) hE)

/-- 選んだ全関手の同じ随伴データ。 -/
def globalSectionsAdjunction
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    QCatAdjunction (constantFunctorMap (presheafShape C) E) (globalSectionsFunctor hE) :=
  Classical.choice (Classical.choose_spec (exists_globalSectionsFunctor (C := C) hE))

/-- 同じ反射と大域切断の合成としての全 RΓ 関手。 -/
def derivedGlobalSectionsFunctor (J : GrothendieckTopology C) (hJ : Sheafification J E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    PresheafCat C E ⟶ E :=
  sheafificationFunctor J hJ ≫ globalSectionsFunctor hE

/-- 元の反射単位を大域切断関手で送った全自然変換。 -/
def globalSectionsToDerivedHom (J : GrothendieckTopology C) (hJ : Sheafification J E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    FunctorHom (globalSectionsFunctor (C := C) hE) (derivedGlobalSectionsFunctor J hJ hE) :=
  (hoFunctor.map ((ihom (PresheafCat C E)).map (globalSectionsFunctor hE))).toFunctor.map
    (Classical.choice hJ).unit

end SerrePositivity.InfinityCategories.Sheaves
