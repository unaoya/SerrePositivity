module

public import SerrePositivity.InfinityCategories.Sheaves.GlobalSectionsConeComparison

/-!
概要：同じ層化と大域切断の全関手から、選択済み RΓ 頂点への射を構成する。
方針：指定錐の adjunct による比較を両端に置き、元の全関手の射を運ぶ。
使われ方：HTT 5.5.2.9・6.2.2.7、Kerodon §7.1（Tag 02H1）の RΓ の関手性。
規約：単位と同じ層化関手を用い、射の類を回収する等式も保持する。
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
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]

/-- 指定 RΓ 頂点と全 RΓ 関手の同じ値との比較。 -/
def derivedGlobalSectionsValueIso (J : GrothendieckTopology C) (hJ : Sheafification J E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (F : Presheaf C E) :
    VertexIso (derivedGlobalSections J hJ hE F)
      ((derivedGlobalSectionsFunctor J hJ hE).app _ (functorVertex F)) :=
  globalSectionsConeValueIso hE (derivedGlobalSectionsCone J hJ hE F)
      (derivedGlobalSectionsCone_isLimit J hJ hE F) ≪≫
    eqToIso (congrArg HomotopyCategory.mk
      (congrArg (fun v ↦ (globalSectionsFunctor hE).app (Opposite.op ⦋0⦌) v)
        (functorVertex_sheafify J hJ F)))

/-- 元の全 RΓ 関手の射を、同じ指定頂点の間へ運んだもの。 -/
def derivedGlobalSectionsHom (J : GrothendieckTopology C) (hJ : Sheafification J E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    {F G : Presheaf C E} (α : FunctorHom F G) :
    HomotopyCategory.mk (derivedGlobalSections J hJ hE F) ⟶
      HomotopyCategory.mk (derivedGlobalSections J hJ hE G) :=
  (derivedGlobalSectionsValueIso J hJ hE F).hom ≫
    (hoFunctor.map (derivedGlobalSectionsFunctor J hJ hE)).toFunctor.map α ≫
      (derivedGlobalSectionsValueIso J hJ hE G).inv

/-- 移送された射は恒等射を保つ。 -/
lemma derivedGlobalSectionsHom_id (J : GrothendieckTopology C) (hJ : Sheafification J E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (F : Presheaf C E) :
    derivedGlobalSectionsHom J hJ hE (𝟙 (HomotopyCategory.mk (functorVertex F))) = 𝟙 _ := by
  simp [derivedGlobalSectionsHom]

/-- 移送された射は合成を保つ。 -/
lemma derivedGlobalSectionsHom_comp (J : GrothendieckTopology C) (hJ : Sheafification J E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    {F G H : Presheaf C E} (α : FunctorHom F G) (β : FunctorHom G H) :
    derivedGlobalSectionsHom J hJ hE (α ≫ β) =
      derivedGlobalSectionsHom J hJ hE α ≫ derivedGlobalSectionsHom J hJ hE β := by
  simp [derivedGlobalSectionsHom, Category.assoc]

/-- 前層の実際のホモトピーを、同じ RΓ 関手による辺で表す。 -/
def derivedGlobalSections_map (J : GrothendieckTopology C) (hJ : Sheafification J E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    {F G : Presheaf C E} (η : SSet.Homotopy F G) :
    E.Edge (derivedGlobalSections J hJ hE F) (derivedGlobalSections J hJ hE G) :=
  let e := Classical.choose (homotopyCategory_homMk_surjective _ _
    (derivedGlobalSectionsHom J hJ hE
      (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy η))))
  ⟨e.edge, e.src_eq, e.tgt_eq⟩

/-- 選んだ辺は元の全関手による射の類そのものを表す。 -/
lemma derivedGlobalSections_map_hom (J : GrothendieckTopology C) (hJ : Sheafification J E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    {F G : Presheaf C E} (η : SSet.Homotopy F G) :
    Truncated.HomotopyCategory.homMk (derivedGlobalSections_map J hJ hE η).toTruncated =
      derivedGlobalSectionsHom J hJ hE
        (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy η)) :=
  Classical.choose_spec (homotopyCategory_homMk_surjective _ _ _)

end SerrePositivity.InfinityCategories.Sheaves
