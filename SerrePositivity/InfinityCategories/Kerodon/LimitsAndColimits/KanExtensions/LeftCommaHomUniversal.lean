module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftCommaHom
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinPrismHom
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftCommaCoconeColimit

/-!
概要：comma 上の標準 Kan 変換の Hom 普遍性を元の指定変換へ戻す。
方針：左端の図式の等式を輸送し、comma の Hom 全単射と候補の指定変換を同定する。
規約：任意の元の関手 δ を許す。
使われ方：局所余極限から大域的に普遍な左 Kan 拡張の構成。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：左 Kan の Hom 普遍性は元の図式の等式による輸送で変わらない。
方針：等式を消去し、Hom の端点の恒等輸送を簡約する。
規約：変換の射を h Fun で輸送する。
使われ方：組み立てた相対 join の左端を元の図式へ戻す。 -/
lemma kanLeftKanHomUniversal_congr_source {K C D : SSet.{u}} (δ : K ⟶ C)
    {F₀ F₀' : K ⟶ D} {F : C ⟶ D} (h : F₀ = F₀') (β : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F₀ (δ ≫ F)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanHomUniversal δ β ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanHomUniversal δ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr h rfl β) := by
  subst F₀'
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr, Iso.homCongr_apply, eqToIso.inv, eqToIso.hom,
    eqToHom_refl, Category.id_comp, Category.comp_id]

/-- 概要：comma 上の指定変換の Hom 普遍性は元の添字への制限後も成立する。
方針：comma の Hom 全単射と底図式の Hom の比較写像を合成し、自然性で同定する。
規約：quasicategory 性や fibration 性はこの移送自体には不要。
使われ方：coherent に構成した Kan 候補の大域的普遍性。 -/
lemma kanLeftCommaHomUniversal {K C D : SSet.{u}} (δ : K ⟶ C)
    {F₀ : K ⟶ D} {F : C ⟶ D}
    (β : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ ≫ F₀) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ ≫ F))
    (hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanHomUniversal (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) β) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanHomUniversal δ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaHomRestriction δ F₀ F β) := by
  intro G
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanHomMap δ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaHomRestriction δ F₀ F β) G =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaHomEquiv δ F₀ G) ∘ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanHomMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) β G := by
    funext τ
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaHomRestriction_comp δ F₀ β τ).symm
  rw [he]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaHomEquiv δ F₀ G).bijective.comp (hβ G)

/-- 概要：候補の指定変換の類は comma 上の標準変換の制限である。
方針：元の図式への左端の等式を輸送し、同じ raw なホモトピーの両端を同定する。
規約：候補の指定変換そのものの類を回収する。
使われ方：元の指定変換に対する Hom 普遍性の結論。 -/
lemma kanLeftCommaCandidateTransformation_hom_restriction {K C D : SSet.{u}}
    (δ : K ⟶ C) (F₀ : K ⟶ D)
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) (𝟙 C) ⟶ D)
    (hH : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) (𝟙 C) ≫ H = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ ≫ F₀) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaHomRestriction δ F₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaCandidate δ H)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr hH rfl (SSet.Truncated.HomotopyCategory.homMk
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
            (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinTransformation (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) H)))) =
      SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaCandidateTransformation δ F₀ H hH)) := by
  have hf : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaInclusion δ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) (𝟙 C) ≫ H) =
      F₀ := by
    rw [hH, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaInclusion_source, Category.id_comp]
  have hg : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaInclusion δ ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) (𝟙 C) ≫ H) =
        δ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaCandidate δ H := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaInclusion_projection]
    rfl
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanHomotopyHom_transport
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinTransformation (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) H)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaInclusion δ)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaCandidateTransformation δ F₀ H hH) hf hg rfl
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp_hom] at hc
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaHomRestriction, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr, Iso.homCongr_apply,
    eqToIso.inv, eqToIso.hom, eqToHom_refl, Category.comp_id,
    CategoryTheory.Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans_assoc]
  exact hc

/-- 概要：局所 fiber で普遍な comma の候補の指定変換は大域的 Hom 普遍性を持つ。
方針：標準 prism の普遍性を左端の等式と comma の Hom 対応で元の添字へ戻す。
規約：元の δ に充填性や単射性は要求しない。
使われ方：局所余極限から指定変換つきの大域的 Kan 拡張を構成する。 -/
lemma kanLeftCommaCandidate_homUniversal {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] (δ : K ⟶ C) (F₀ : K ⟶ D)
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) (𝟙 C) ⟶ D)
    (hH : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) (𝟙 C) ≫ H = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ ≫ F₀)
    (hcol : ∀ c : C _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinFiberCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) c H)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanHomUniversal δ (SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaCandidateTransformation δ F₀ H hH))) := by
  have hu := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinTransformation_homUniversal (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) H hcol
  have hv := (kanLeftKanHomUniversal_congr_source (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) hH _).1 hu
  have hw := kanLeftCommaHomUniversal δ _ hv
  erw [kanLeftCommaCandidateTransformation_hom_restriction δ F₀ H hH] at hw
  exact hw

/-- 概要：局所余極限があれば点ごとの Kan 条件と大域的 Hom 普遍性を同時に持つ拡張を得る。
方針：同じ comma の普遍図式から候補と指定変換を取り出し、両方の普遍性を使う。
規約：同じ宇宙の quasicategory 間の任意の δ を扱う。
使われ方：任意の既存の Kan 拡張との比較のための大域的に普遍な候補。 -/
lemma exists_kanLeftExtension_with_homUniversal_of_local_colimits {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] (δ : K ⟶ C) (F₀ : K ⟶ D)
    (hcol : ∀ c : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram δ F₀ c)) :
    ∃ (F : C ⟶ D) (β : SSet.Homotopy F₀ (δ ≫ F)), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension δ F₀ F β ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanHomUniversal δ
        (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy β)) := by
  obtain ⟨H, hH, hc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanLeftComma_diagram_with_colimit_fibers δ F₀ hcol
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaCandidate δ H, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaCandidateTransformation δ F₀ H hH,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaCandidate_isLeftKanExtension δ F₀ H hH hc,
    kanLeftCommaCandidate_homUniversal δ F₀ H hH hc⟩

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
