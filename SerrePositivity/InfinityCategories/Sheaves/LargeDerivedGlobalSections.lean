module

public import SerrePositivity.InfinityCategories.Sheaves.LargeGlobalSectionsSiteComparison
public import SerrePositivity.InfinityCategories.Sheaves.Sheafification
public import SerrePositivity.InfinityCategories.Sheaves.SheafGlobalSectionsFamily

/-!
概要：本質的小さい大きい site の全前層の RΓ を、小さい模型の元の反射で定義する。
方針：全再添字・元の指定層化・Γ を合成し、元の大きい Γ との全単位比較を保持する。
  文献対応：BS Remark 4.5、HTT 6.2.2.7、Kerodon §6.2（Tag 02EH）の小さい模型での層化。
規約：設計どおり層化は SmallModel で行う。係数 SSet(u+1)、元の全前層を定義域とする。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type (u + 1)} [Category.{u} C] {D : Type u} [SmallCategory D]
variable {E : SSet.{u + 1}} [Quasicategory E]

/-- 小さい模型の同じ指定反射による、元の大きい全前層上の RΓ 全関手。 -/
def largeDerivedGlobalSectionsFunctor (e : D ≌ C) (J : GrothendieckTopology D)
    (hJ : Sheafification J E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    LargePresheafCat C E ⟶ E :=
  reindexSmallModelPresheafFunctor e E ≫ derivedGlobalSectionsFunctor J hJ hE

/-- 元の大きい Γ から RΓ への全自然変換は、小さい模型の同じ層化単位から得る。 -/
def largeGlobalSectionsToDerivedHom (e : D ≌ C) (J : GrothendieckTopology D)
    (hJ : Sheafification J E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    FunctorHom (largeGlobalSectionsFunctor e hE) (largeDerivedGlobalSectionsFunctor e J hJ hE) :=
  (globalSectionsSmallModelFunctorIso e hE).inv ≫
    (hoFunctor.map ((pre (reindexSmallModelPresheafFunctor e E)).app E)).toFunctor.map
      (globalSectionsToDerivedHom J hJ hE)

/-- 元の大きい層の全族では、小さい模型の同じ指定単位から Γ と RΓ の同型を得る。 -/
def largeSheafGlobalSectionsUnitIso (e : D ≌ C)
    (J : GrothendieckTopology D) (K : GrothendieckTopology C)
    (hf : CoverPreserving J K e.functor) (hg : CoverPreserving K J e.inverse)
    (hJ : Sheafification J E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    FunctorIso (largeSheafInclusion K ≫ largeGlobalSectionsFunctor e hE)
      (largeSheafInclusion K ≫ largeDerivedGlobalSectionsFunctor e J hJ hE) := by
  let a := (globalSectionsSmallModelFunctorIso e hE).precomp (largeSheafInclusion K)
  let b := sheafGlobalSectionsUnitIso J hJ hE (reindexLargeSheafFunctor e J K hf hg)
  simp only [← Category.assoc, reindexLargeSheafFunctor_comp] at b
  simpa only [largeDerivedGlobalSectionsFunctor, Category.assoc] using a.symm ≪≫ b

/-- 元の EssentiallySmall 入力と係数の presentable 性から、小さい模型の RΓ を定義する。 -/
def essentiallySmallDerivedGlobalSectionsFunctor [EssentiallySmall.{u} C]
    (J : GrothendieckTopology C)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    LargePresheafCat C E ⟶ E :=
  largeDerivedGlobalSectionsFunctor (equivSmallModel.{u} C).symm
    ((equivSmallModel.{u} C).inverse.inducedTopology J)
    (sheafification_exists _ hE) hE

/-- 元の本質的小さい site の全層では、同じ模型の単位で元の Γ と RΓ が一致する。 -/
def essentiallySmallSheafGlobalSectionsUnitIso [EssentiallySmall.{u} C]
    (J : GrothendieckTopology C)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    FunctorIso (largeSheafInclusion J ≫ largeGlobalSectionsFunctor (equivSmallModel.{u} C).symm hE)
      (largeSheafInclusion J ≫ essentiallySmallDerivedGlobalSectionsFunctor J hE) := by
  let e : SmallModel.{u} C ≌ C := (equivSmallModel.{u} C).symm
  letI : (equivSmallModel.{u} C).functor.IsDenseSubsite J
      ((equivSmallModel.{u} C).inverse.inducedTopology J) := by infer_instance
  exact largeSheafGlobalSectionsUnitIso e (e.functor.inducedTopology J) J
    (CoverPreserving.of_isContinuous (F := e.functor) (e.functor.inducedTopology J) J)
    (Functor.IsDenseSubsite.coverPreserving J
      ((equivSmallModel.{u} C).inverse.inducedTopology J) (equivSmallModel.{u} C).functor)
    (sheafification_exists _ hE) hE

end SerrePositivity.InfinityCategories.Sheaves
