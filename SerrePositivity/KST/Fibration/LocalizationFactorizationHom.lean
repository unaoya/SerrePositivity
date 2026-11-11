module
public import SerrePositivity.KST.LocalizingInvariants.LocalizationUniqueness
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyRepresentative

/-! # 全関手 ∞ 圏の局所化普遍性による、同じ比較二胞体の実持ち上げ -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {X Q Y : SSet.{u}} [Quasicategory Q] [Quasicategory Y]
  (q : X ⟶ Q) (W : Set (X _⦋1⦌)) (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization q W)
  {K L : Q ⟶ Y}

/-- 実際の全関手圏の写像空間の充満忠実性から、指定した同じ二胞体の逆像を取る。 -/
def localizationFactorizationHom (a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (q ≫ K) (q ≫ L)) : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom K L :=
  (localizationPre_fullyFaithful q W hq).toHoFullyFaithful.preimage a

/-- 同じ局所化で制限すると、指定された元の比較二胞体そのものを回収する。 -/
theorem localizationFactorizationHom_map (a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (q ≫ K) (q ≫ L)) :
    (hoFunctor.map ((pre q).app Y)).toFunctor.map (localizationFactorizationHom q W hq a) = a :=
  (localizationPre_fullyFaithful (Y := Y) q W hq).toHoFullyFaithful.map_preimage
    (X := HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex K))
    (Y := HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex L)) a

/-- 同じ持ち上げは、全関手圏の中の実際の単体的ホモトピーとして表示できる。 -/
def localizationFactorizationHomotopy (a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (q ≫ K) (q ≫ L)) : SSet.Homotopy K L :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy (localizationFactorizationHom q W hq a)

/-- 選んだホモトピー代表の類は、同じ持ち上げた二胞体と厳密に一致する。 -/
theorem localizationFactorizationHomotopy_hom (a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (q ≫ K) (q ≫ L)) :
    Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (localizationFactorizationHomotopy q W hq a)) =
        localizationFactorizationHom q W hq a := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy_hom _

end SerrePositivity.KST.Fibration
