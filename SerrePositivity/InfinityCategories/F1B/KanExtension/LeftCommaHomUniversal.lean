module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftCommaHom
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeJoinPrismHom
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftCommaCoconeColimit

/-!
概要：comma 上の標準 Kan 変換の Hom 普遍性を元の指定変換へ戻す。
方針：左端の図式の等式を輸送し、comma の Hom 全単射と候補の指定変換を同定する。
規約：任意の元の関手 δ を許す。
使われ方：局所余極限から大域的に普遍な左 Kan 拡張の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：左 Kan の Hom 普遍性は元の図式の等式による輸送で変わらない。
方針：等式を消去し、Hom の端点の恒等輸送を簡約する。
規約：変換の射を h Fun で輸送する。
使われ方：組み立てた相対 join の左端を元の図式へ戻す。 -/
lemma kanLeftKanHomUniversal_congr_source {K C D : SSet.{u}} (δ : K ⟶ C)
    {F₀ F₀' : K ⟶ D} {F : C ⟶ D} (h : F₀ = F₀') (β : FunctorHom F₀ (δ ≫ F)) :
    LeftKanHomUniversal δ β ↔ LeftKanHomUniversal δ (kanFunctorHomCongr h rfl β) := by
  subst F₀'
  simp only [kanFunctorHomCongr, Iso.homCongr_apply, eqToIso.inv, eqToIso.hom,
    eqToHom_refl, Category.id_comp, Category.comp_id]

/-- 概要：comma 上の指定変換の Hom 普遍性は元の添字への制限後も成立する。
方針：comma の Hom 全単射と底図式の Hom の比較写像を合成し、自然性で同定する。
規約：quasicategory 性や fibration 性はこの移送自体には不要。
使われ方：coherent に構成した Kan 候補の大域的普遍性。 -/
lemma kanLeftCommaHomUniversal {K C D : SSet.{u}} (δ : K ⟶ C)
    {F₀ : K ⟶ D} {F : C ⟶ D}
    (β : FunctorHom (kanLeftCommaSource δ ≫ F₀) (kanLeftCommaProjection δ ≫ F))
    (hβ : LeftKanHomUniversal (kanLeftCommaProjection δ) β) :
    LeftKanHomUniversal δ (kanLeftCommaHomRestriction δ F₀ F β) := by
  intro G
  have he : leftKanHomMap δ (kanLeftCommaHomRestriction δ F₀ F β) G =
      (kanLeftCommaHomEquiv δ F₀ G) ∘ leftKanHomMap (kanLeftCommaProjection δ) β G := by
    funext τ
    exact (kanLeftCommaHomRestriction_comp δ F₀ β τ).symm
  rw [he]
  exact (kanLeftCommaHomEquiv δ F₀ G).bijective.comp (hβ G)

/-- 概要：候補の指定変換の類は comma 上の標準変換の制限である。
方針：元の図式への左端の等式を輸送し、同じ raw なホモトピーの両端を同定する。
規約：候補の指定変換そのものの類を回収する。
使われ方：元の指定変換に対する Hom 普遍性の結論。 -/
lemma kanLeftCommaCandidateTransformation_hom_restriction {K C D : SSet.{u}}
    (δ : K ⟶ C) (F₀ : K ⟶ D)
    (H : relativeJoin (kanLeftCommaProjection δ) (𝟙 C) ⟶ D)
    (hH : relativeJoinInl (kanLeftCommaProjection δ) (𝟙 C) ≫ H = kanLeftCommaSource δ ≫ F₀) :
    kanLeftCommaHomRestriction δ F₀ (kanLeftCommaCandidate δ H)
        (kanFunctorHomCongr hH rfl (SSet.Truncated.HomotopyCategory.homMk
          (functorEdgeOfSimplicialHomotopy
            (kanRelativeJoinTransformation (kanLeftCommaProjection δ) H)))) =
      SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (kanLeftCommaCandidateTransformation δ F₀ H hH)) := by
  have hf : kanLeftCommaInclusion δ ≫ (relativeJoinInl (kanLeftCommaProjection δ) (𝟙 C) ≫ H) =
      F₀ := by
    rw [hH, ← Category.assoc, kanLeftCommaInclusion_source, Category.id_comp]
  have hg : kanLeftCommaInclusion δ ≫
      (kanLeftCommaProjection δ ≫ relativeJoinInr (kanLeftCommaProjection δ) (𝟙 C) ≫ H) =
        δ ≫ kanLeftCommaCandidate δ H := by
    rw [← Category.assoc, kanLeftCommaInclusion_projection]
    rfl
  have hc := kanHomotopyHom_transport
    (functorHomotopyPrecomp (kanRelativeJoinTransformation (kanLeftCommaProjection δ) H)
      (kanLeftCommaInclusion δ)) (kanLeftCommaCandidateTransformation δ F₀ H hH) hf hg rfl
  rw [functorHomotopyPrecomp_hom] at hc
  simp only [kanLeftCommaHomRestriction, kanFunctorHomCongr, Iso.homCongr_apply,
    eqToIso.inv, eqToIso.hom, eqToHom_refl, Category.comp_id,
    CategoryTheory.Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans_assoc]
  exact hc

/-- 概要：局所 fiber で普遍な comma の候補の指定変換は大域的 Hom 普遍性を持つ。
方針：標準 prism の普遍性を左端の等式と comma の Hom 対応で元の添字へ戻す。
規約：元の δ に充填性や単射性は要求しない。
使われ方：局所余極限から指定変換つきの大域的 Kan 拡張を構成する。 -/
lemma kanLeftCommaCandidate_homUniversal {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] (δ : K ⟶ C) (F₀ : K ⟶ D)
    (H : relativeJoin (kanLeftCommaProjection δ) (𝟙 C) ⟶ D)
    (hH : relativeJoinInl (kanLeftCommaProjection δ) (𝟙 C) ≫ H = kanLeftCommaSource δ ≫ F₀)
    (hcol : ∀ c : C _⦋0⦌,
      IsColimitCone (kanRelativeJoinFiberCocone (kanLeftCommaProjection δ) c H)) :
    LeftKanHomUniversal δ (SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (kanLeftCommaCandidateTransformation δ F₀ H hH))) := by
  have hu := kanRelativeJoinTransformation_homUniversal (kanLeftCommaProjection δ) H hcol
  have hv := (kanLeftKanHomUniversal_congr_source (kanLeftCommaProjection δ) hH _).1 hu
  have hw := kanLeftCommaHomUniversal δ _ hv
  erw [kanLeftCommaCandidateTransformation_hom_restriction δ F₀ H hH] at hw
  exact hw

/-- 概要：局所余極限があれば点ごとの Kan 条件と大域的 Hom 普遍性を同時に持つ拡張を得る。
方針：同じ comma の普遍図式から候補と指定変換を取り出し、両方の普遍性を使う。
規約：同じ宇宙の quasicategory 間の任意の δ を扱う。
使われ方：任意の既存の Kan 拡張との比較のための大域的に普遍な候補。 -/
lemma exists_kanLeftExtension_with_homUniversal_of_local_colimits {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] (δ : K ⟶ C) (F₀ : K ⟶ D)
    (hcol : ∀ c : C _⦋0⦌, HasColimit (leftKanDiagram δ F₀ c)) :
    ∃ (F : C ⟶ D) (β : SSet.Homotopy F₀ (δ ≫ F)), IsLeftKanExtension δ F₀ F β ∧
      LeftKanHomUniversal δ
        (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy β)) := by
  obtain ⟨H, hH, hc⟩ := exists_kanLeftComma_diagram_with_colimit_fibers δ F₀ hcol
  exact ⟨kanLeftCommaCandidate δ H, kanLeftCommaCandidateTransformation δ F₀ H hH,
    kanLeftCommaCandidate_isLeftKanExtension δ F₀ H hH hc,
    kanLeftCommaCandidate_homUniversal δ F₀ H hH hc⟩

end SerrePositivity.InfinityCategories.F1B
