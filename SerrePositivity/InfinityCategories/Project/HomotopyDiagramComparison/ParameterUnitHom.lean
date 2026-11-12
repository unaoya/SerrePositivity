module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitHomFormula
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.PrecompositionHomotopy

/-!
概要：任意の単体集合パラメータ上で、同じ指定単位による標準 Hom 写像と三つの自然性。
方針：inner anodyne な制限の充満忠実性と、元の単位の式の自然性を使う。
規約：native な錐の極限性への接続は別工程。使われ方：一般 coherent 極限の保存。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 指定単位の標準 Hom 写像を、パラメータの quasicategory 性なしに定義する。 -/
def parameterUnitHomMap {A X Y : SSet.{u}} {F : X ⟶ Y} {G : Y ⟶ X}
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)) (U : A ⟶ X) (V : A ⟶ Y)
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (U ≫ F) V) : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U (V ≫ G) :=
  (hoFunctor.map ((pre U).app X)).toFunctor.map η ≫
    (hoFunctor.map ((ihom A).map G)).toFunctor.map α

/-- quasicategory パラメータ上では、元の標準単位の Hom 写像と一致する。 -/
lemma parameterUnitHomMap_eq {A X Y : SSet.{u}}
    [Quasicategory A] [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G))
    (U : A ⟶ X) (V : A ⟶ Y) (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (U ≫ F) V) :
    parameterUnitHomMap η U V α = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitHomMap η U V α :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitHomMap_formula η U V α).symm

/-- 元の標準単位の写像は、任意のパラメータ写像による制限と可換である。 -/
lemma parameterUnitHomMap_precomp {A B X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G))
    (k : A ⟶ B) (U : B ⟶ X) (V : B ⟶ Y) (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (U ≫ F) V) :
    parameterUnitHomMap η (k ≫ U) (k ≫ V)
        ((hoFunctor.map ((pre k).app Y)).toFunctor.map α) =
      (hoFunctor.map ((pre k).app X)).toFunctor.map (parameterUnitHomMap η U V α) := by
  have hη : (hoFunctor.map ((pre (k ≫ U)).app X)).toFunctor.map η =
      (hoFunctor.map ((pre k).app X)).toFunctor.map
        ((hoFunctor.map ((pre U).app X)).toFunctor.map η) := by
    obtain ⟨e, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _ η
    rfl
  have hα : (hoFunctor.map ((ihom A).map G)).toFunctor.map
      ((hoFunctor.map ((pre k).app Y)).toFunctor.map α) =
    (hoFunctor.map ((pre k).app X)).toFunctor.map
      ((hoFunctor.map ((ihom B).map G)).toFunctor.map α) := by
    obtain ⟨e, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _ α
    rfl
  unfold parameterUnitHomMap
  rw [hη, hα, CategoryTheory.Functor.map_comp]

/-- 標準単位の写像は、任意の終域側の二胞体による合成に自然である。 -/
lemma parameterUnitHomMap_naturality_right {A X Y : SSet.{u}}
    {F : X ⟶ Y} {G : Y ⟶ X} (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G))
    (U : A ⟶ X) {V V' : A ⟶ Y} (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (U ≫ F) V) (β : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom V V') :
    parameterUnitHomMap η U V' (α ≫ β) = parameterUnitHomMap η U V α ≫
      (hoFunctor.map ((ihom A).map G)).toFunctor.map β := by
  simp only [parameterUnitHomMap, CategoryTheory.Functor.map_comp, Category.assoc]

/-- 標準単位の写像は、任意の始域側の二胞体による合成にも自然である。 -/
lemma parameterUnitHomMap_naturality_left {A X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)) {U U' : A ⟶ X} {V : A ⟶ Y}
    (γ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U' U) (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (U ≫ F) V) :
    parameterUnitHomMap η U' V ((hoFunctor.map ((ihom A).map F)).toFunctor.map γ ≫ α) =
      γ ≫ parameterUnitHomMap η U V α := by
  have hn := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.precompositionNatTrans (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy γ) X).naturality η
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.precompositionNatTrans_app, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.precompositionNatTrans_app,
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom,
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy_hom] at hn
  have hid : (hoFunctor.map ((ihom A).map (𝟙 X))).toFunctor.map γ = γ := by
    obtain ⟨e, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _ γ
    rfl
  rw [hid] at hn
  have hγ : (hoFunctor.map ((ihom A).map G)).toFunctor.map
      ((hoFunctor.map ((ihom A).map F)).toFunctor.map γ) =
      (hoFunctor.map ((ihom A).map (F ≫ G))).toFunctor.map γ := by
    obtain ⟨e, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _ γ
    rfl
  unfold parameterUnitHomMap
  rw [CategoryTheory.Functor.map_comp, ← Category.assoc, hγ, hn, Category.assoc]

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
