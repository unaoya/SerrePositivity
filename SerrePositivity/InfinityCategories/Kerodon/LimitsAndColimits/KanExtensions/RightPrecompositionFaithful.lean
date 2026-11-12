module
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FullSubcomplexMapping
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightHomUniversal
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.PrecompositionFullFaithfulness
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Localization
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulCalculus
/-!
概要：各関手が自分の制限の恒等変換による右 Kan 拡張なら、前合成は全写像空間で充満忠実。
方針：右 Kan の Hom 普遍性を全標的で使い、内部 Hom の交換による全パラメータ判定へ渡す。
規約：h Fun のみの結論で止めない。使われ方：商関手の局所化普遍性の充満忠実性。

対応節は Kerodon 7.3（Tag 02Y1）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
/-- 標準右 Kan 変換の Hom 普遍性は、指定した前合成写像そのものの全単射性。 -/
lemma rightKanRefl_homMap_bijective {X Q Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Q] [Quasicategory Y] (q : X ⟶ Q) (F G : Q ⟶ Y)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension q (q ≫ G) G (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl (q ≫ G))) :
    Function.Bijective ((hoFunctor.map ((pre q).app Y)).toFunctor.map :
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F G → _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (q ≫ F) (q ≫ G)) := by
  have hu := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightKanExtension_homUniversal q (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl (q ≫ G)) h F
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanHomMap q
      (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl (q ≫ G)))) F =
      ((hoFunctor.map ((pre q).app Y)).toFunctor.map :
        _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F G → _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (q ≫ F) (q ≫ G)) := by
    funext η
    change _ ≫ Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl (q ≫ G))) = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl_hom]
    exact Category.comp_id ((hoFunctor.map ((pre q).app Y)).toFunctor.map η)
  exact he ▸ hu
/-- 各関手の標準右 Kan 条件は、指定標的の h Fun における前合成の充満忠実性を与える。 -/
def rightKanPrecompositionHoFullyFaithful {X Q Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Q] [Quasicategory Y] (q : X ⟶ Q)
    (h : ∀ G : Q ⟶ Y, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension q (q ≫ G) G (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl (q ≫ G))) :
    (hoFunctor.map ((pre q).app Y)).toFunctor.FullyFaithful := by
  have hb (a b : hoFunctor.obj ((ihom Q).obj Y)) : Function.Bijective
      ((hoFunctor.map ((pre q).app Y)).toFunctor.map : (a ⟶ b) → _) := by
    obtain ⟨x, rfl⟩ := Truncated.HomotopyCategory.mk_surjective a
    obtain ⟨y, rfl⟩ := Truncated.HomotopyCategory.mk_surjective b
    obtain ⟨F, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Q Y).surjective x
    obtain ⟨G, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Q Y).surjective y
    exact rightKanRefl_homMap_bijective q F G (h G)
  have : (hoFunctor.map ((pre q).app Y)).toFunctor.Full := ⟨fun {a b} => (hb a b).2⟩
  have : (hoFunctor.map ((pre q).app Y)).toFunctor.Faithful := ⟨fun {a b} => (hb a b).1⟩
  exact CategoryTheory.Functor.FullyFaithful.ofFullyFaithful _
/-- 全標的での標準右 Kan 条件は、局所化前合成の全写像空間上の充満忠実性を与える。 -/
lemma localizationPrecomposition_isFullyFaithful_of_rightKan {X Q : SSet.{u}}
    [Quasicategory X] [Quasicategory Q] (q : X ⟶ Q) (W : Set (X _⦋1⦌))
    (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges q W)
    (h : ∀ (Y : SSet.{u}) [Quasicategory Y], ∀ G : Q ⟶ Y,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension q (q ≫ G) G (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl (q ≫ G)))
    (Y : SSet.{u}) [Quasicategory Y] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition q W hq Y) := by
  have hp := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.precomposition_isFullyFaithful_of_hoFullyFaithful q
    (fun Z _ => rightKanPrecompositionHoFullyFaithful q (h Z)) Y
  have hi := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι ((ihom X).obj Y)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsInvertingFunctorVertex X Y W)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors X Y W).ι at hi
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition q W hq Y ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors X Y W).ι) :=
    (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition_ι q W hq Y)).mpr hp
  exact hi.cancel_right hc
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
