module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorOppositeHom
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightOppositeCriterion
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftHomUniversal

/-!
概要：任意の指定右 Kan 変換の大域的 Hom 普遍性と一意性。
方針：指定変換を反転し、左 Kan の普遍性を反転 Hom 全単射で戻す。
規約：元の指定変換の類による比較写像そのものを扱う。
使われ方：点ごとの右 Kan 条件から大域的な普遍写像性への接続。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：右 Kan の Hom 比較は反転 Hom 対応で左 Kan の比較へ移る。
方針：反転による合成順序の交換、前合成公式、指定変換の辺の公式を使う。
規約：Kan 条件はまだ仮定しない。
使われ方：左比較写像の全単射性を右比較写像へ移す。 -/
lemma kanRightKanHomMap_opposite {K C D : SSet.{u}} [Quasicategory D]
    (δ : K ⟶ C) {F₀ : K ⟶ D} {F : C ⟶ D}
    (α : SSet.Homotopy (δ ≫ F) F₀) (G : C ⟶ D) (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom G F) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorOppositeHomEquiv (δ ≫ G) F₀
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanHomMap δ
          (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy α)) G η) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanHomMap (SSet.opFunctor.map δ)
        (SSet.Truncated.HomotopyCategory.homMk
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanOppositeTransformation δ F₀ F α)))
        (SSet.opFunctor.map G) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorOppositeHomEquiv G F η) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanHomMap, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanHomMap]
  erw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorOppositeHomEquiv_comp
    (F := δ ≫ G) (G := δ ≫ F) (H := F₀)
    ((hoFunctor.map ((pre δ).app D)).toFunctor.map η)
    (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy α))]
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorOppositeHomEquiv_precomp, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorOppositeHomEquiv_homotopy]
  rfl

/-- 概要：任意の指定右 Kan 変換は h Fun の大域的 Hom 普遍性を持つ。
方針：反転した指定変換の左普遍性と Hom 全単射の可換な比較で戻す。
規約：元の α 自身の類の比較写像を結論する。
使われ方：右 Kan 拡張の大域的一意性。 -/
lemma kanRightKanExtension_homUniversal {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] (δ : K ⟶ C)
    {F₀ : K ⟶ D} {F : C ⟶ D} (α : SSet.Homotopy (δ ≫ F) F₀)
    (hα : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension δ F₀ F α) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanHomUniversal δ
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy α)) := by
  have hu := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftKanExtension_homUniversal (SSet.opFunctor.map δ)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanOppositeTransformation δ F₀ F α) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanIsRightKanExtension_opposite δ F₀ F α hα)
  intro G
  let e := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorOppositeHomEquiv (δ ≫ G) F₀
  have he := (hu (SSet.opFunctor.map G)).comp (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorOppositeHomEquiv G F).bijective
  have hf :
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanHomMap (SSet.opFunctor.map δ)
        (SSet.Truncated.HomotopyCategory.homMk
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanOppositeTransformation δ F₀ F α)))
        (SSet.opFunctor.map G)) ∘ (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorOppositeHomEquiv G F) =
      e ∘ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanHomMap δ
        (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy α)) G) := by
    funext η
    exact (kanRightKanHomMap_opposite δ α G η).symm
  rw [hf] at he
  constructor
  · intro a b hab
    exact he.1 (congrArg e hab)
  · intro β
    obtain ⟨η, hη⟩ := he.2 (e β)
    exact ⟨η, e.injective hη⟩

/-- 概要：h Fun の指定射の右 Kan 条件からその射の Hom 普遍性を得る。
方針：ホモトピー代表に適用して代表の類を戻す。
規約：結論に代表の選択を残さない。
使われ方：h Fun の自然変換で与える利用側の界面。 -/
lemma kanRightKanExtensionHom_homUniversal {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] (δ : K ⟶ C)
    (F₀ : K ⟶ D) (F : C ⟶ D) (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (δ ≫ F) F₀)
    (hα : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtensionHom δ F₀ F α) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanHomUniversal δ α := by
  have h := kanRightKanExtension_homUniversal δ (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy α) hα
  rwa [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy_hom] at h

/-- 概要：指定変換に両立する二つの右 Kan 拡張の大域的比較同型。
方針：両方の右 Hom 普遍性から比較同型を作る。
規約：同型は h Fun(C,D) の同型である。
使われ方：右 Kan 拡張の大域的一意性。 -/
def kanRightKanExtensionIso {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] (δ : K ⟶ C)
    {F₀ : K ⟶ D} {F G : C ⟶ D}
    (α : SSet.Homotopy (δ ≫ F) F₀) (β : SSet.Homotopy (δ ≫ G) F₀)
    (hα : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension δ F₀ F α) (hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension δ F₀ G β) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanHomUniversalIso δ _ _ (kanRightKanExtension_homUniversal δ α hα)
    (kanRightKanExtension_homUniversal δ β hβ)

/-- 概要：右 Kan 比較同型は指定された二つの変換に両立する。
方針：普遍比較同型を選んだ全射性の仕様を使う。
規約：元の指定変換の類を比較する。
使われ方：指定変換を保持する同型の回収。 -/
lemma kanRightKanExtensionIso_hom_fac {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] (δ : K ⟶ C)
    {F₀ : K ⟶ D} {F G : C ⟶ D}
    (α : SSet.Homotopy (δ ≫ F) F₀) (β : SSet.Homotopy (δ ≫ G) F₀)
    (hα : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension δ F₀ F α) (hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension δ F₀ G β) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanHomMap δ (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy β)) F
        (kanRightKanExtensionIso δ α β hα hβ).hom =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy α) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanHomUniversalIso_hom_fac δ _ _ (kanRightKanExtension_homUniversal δ α hα)
    (kanRightKanExtension_homUniversal δ β hβ)

/-- 概要：指定変換に両立する右 Kan 比較射は構成した同型の射に一意。
方針：右 Hom 比較写像の単射性を使う。
規約：射の等式は h Fun(C,D) 全体で成立する。
使われ方：変換を保持した右 Kan 拡張の大域的一意性。 -/
lemma kanRightKanExtensionIso_hom_unique {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] (δ : K ⟶ C)
    {F₀ : K ⟶ D} {F G : C ⟶ D}
    (α : SSet.Homotopy (δ ≫ F) F₀) (β : SSet.Homotopy (δ ≫ G) F₀)
    (hα : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension δ F₀ F α) (hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension δ F₀ G β)
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F G)
    (hη : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanHomMap δ (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy β)) F η =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy α)) :
    η = (kanRightKanExtensionIso δ α β hα hβ).hom :=
  (kanRightKanExtension_homUniversal δ β hβ F).1
    (hη.trans (kanRightKanExtensionIso_hom_fac δ α β hα hβ).symm)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
