module
public import SerrePositivity.KST.Fibration.SpaceLocalizationPreFaithful
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyRepresentative

/-! # 元の空間値比較二胞体の、宇宙を揃えた商への実降下 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {X Q : SSet.{u}} [Quasicategory Q] (q : X ⟶ Q)
  (W : Set (X _⦋1⦌)) (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization q W)
  {K L : (SSet.uliftFunctor.{u + 1, u}).obj Q ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}}

/-- 元の全写像空間で証明した充満忠実性により、同じ指定比較二胞体を商へ持ち上げる。 -/
def spaceLocalizationFactorizationHom
    (a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom ((SSet.uliftFunctor.{u + 1, u}).map q ≫ K)
      ((SSet.uliftFunctor.{u + 1, u}).map q ≫ L)) : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom K L :=
  (spaceLocalizationPre_fullyFaithful q W hq).toHoFullyFaithful.preimage a

/-- 同じ商関手に沿う制限は、元の指定二胞体そのものを厳密に回収する。 -/
theorem spaceLocalizationFactorizationHom_map
    (a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom ((SSet.uliftFunctor.{u + 1, u}).map q ≫ K)
      ((SSet.uliftFunctor.{u + 1, u}).map q ≫ L)) :
    (hoFunctor.map ((pre ((SSet.uliftFunctor.{u + 1, u}).map q)).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity)).toFunctor.map
      (spaceLocalizationFactorizationHom q W hq a) = a :=
  (spaceLocalizationPre_fullyFaithful q W hq).toHoFullyFaithful.map_preimage
    (X := HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex K))
    (Y := HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex L)) a

/-- 同じ商上の比較二胞体の実際のホモトピー表示。 -/
def spaceLocalizationFactorizationHomotopy
    (a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom ((SSet.uliftFunctor.{u + 1, u}).map q ≫ K)
      ((SSet.uliftFunctor.{u + 1, u}).map q ≫ L)) : SSet.Homotopy K L :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy (spaceLocalizationFactorizationHom q W hq a)

end SerrePositivity.KST.Fibration
