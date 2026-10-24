module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftCommaUniversalCriterion
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeLeftClassStrictification

/-!
概要：底の普遍図式の上の comma 候補の単位の像は恒等の類となる。
方針：右端で底の図式を回収し、普遍自己変換の類の恒等性を移す。
規約：候補の指定単位の両端の輸送も計算する。
使われ方：局所相対余極限からの大域構成を元と標的を保つ厳密化へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：底の普遍図式上の comma 候補は標的図式を厳密に回収する。
方針：右端へ制限し、普遍図式の右端が恒等であることを使う。
規約：元の図式の左端条件は不要。
使われ方：相対左 Kan 厳密化で固定する底の図式の識別。 -/
lemma kanLeftCommaCandidate_postcomp {K C D E : SSet.{u}} [Quasicategory C]
    (δ : K ⟶ C) (U : D ⟶ E)
    (H : relativeJoin (kanLeftCommaProjection δ) (𝟙 C) ⟶ D) (H₀ : C ⟶ E)
    (hHU : H ≫ U = kanLeftCommaUniversalDiagram δ ≫ H₀) :
    kanLeftCommaCandidate δ H ≫ U = H₀ := by
  change (relativeJoinInr (kanLeftCommaProjection δ) (𝟙 C) ≫ H) ≫ U = H₀
  rw [Category.assoc, hHU, ← Category.assoc, kanLeftCommaUniversalDiagram_inr, Category.id_comp]

/-- 概要：底の普遍図式上の候補の単位の像は等式の恒等射の類。
方針：元の指定単位を底の普遍自己変換と比較し、端点の等式による輸送を消す。
規約：底での単位の代表が定値とは仮定しない。
使われ方：元と底の図式を同時に保つ相対左 Kan 厳密化の入力。 -/
lemma kanLeftCommaCandidateTransformation_image_class {K C D E : SSet.{u}}
    [Quasicategory C] (δ : K ⟶ C) (U : D ⟶ E) (F₀ : K ⟶ D)
    (H : relativeJoin (kanLeftCommaProjection δ) (𝟙 C) ⟶ D)
    (hH : relativeJoinInl (kanLeftCommaProjection δ) (𝟙 C) ≫ H = kanLeftCommaSource δ ≫ F₀)
    (H₀ : C ⟶ E) (hFU : F₀ ≫ U = δ ≫ H₀)
    (hHU : H ≫ U = kanLeftCommaUniversalDiagram δ ≫ H₀)
    (hc : F₀ ≫ U = (δ ≫ kanLeftCommaCandidate δ H) ≫ U) :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (functorHomotopyPostcomp (kanLeftCommaCandidateTransformation δ F₀ H hH) U)) =
      eqToHom (congrArg (fun q : K ⟶ E ↦ HomotopyCategory.mk (functorVertex q)) hc) := by
  let β := functorHomotopyPostcomp (kanLeftCommaCandidateTransformation δ F₀ H hH) U
  let α := functorHomotopyPostcomp (kanLeftCommaUniversalIdentityHomotopy δ) H₀
  have h₁ : (δ ≫ kanLeftCommaCandidate δ H) ≫ U = δ ≫ H₀ := by
    rw [Category.assoc, kanLeftCommaCandidate_postcomp δ U H H₀ hHU]
  have hraw : β.h = α.h := by
    change ((kanLeftCommaInclusion δ) ▷ (Δ[1] : SSet.{u})) ≫
      ((β_ (kanLeftComma δ) (Δ[1] : SSet.{u})).hom ≫
        relativeJoinPrism (kanLeftCommaProjection δ) ≫ H) ≫ U =
      ((kanLeftCommaInclusion δ) ▷ (Δ[1] : SSet.{u})) ≫
        ((β_ (kanLeftComma δ) (Δ[1] : SSet.{u})).hom ≫
          relativeJoinPrism (kanLeftCommaProjection δ) ≫ kanLeftCommaUniversalDiagram δ) ≫ H₀
    simp only [Category.assoc, hHU]
  have ht := kanHomotopyHom_transport β α hFU h₁ hraw
  have hα : SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy α) =
      𝟙 (HomotopyCategory.mk (functorVertex (δ ≫ H₀))) := by
    rw [kanLeftCommaUniversalIdentityHomotopy_postcomp_hom, functorHomotopyRefl_hom]
  rw [hα] at ht
  apply (cancel_epi (eqToHom
    (congrArg (fun q : K ⟶ E ↦ HomotopyCategory.mk (functorVertex q)) hFU).symm)).1
  apply (cancel_mono (eqToHom
    (congrArg (fun q : K ⟶ E ↦ HomotopyCategory.mk (functorVertex q)) h₁))).1
  simpa only [Category.assoc, eqToHom_trans, eqToHom_refl] using ht

end SerrePositivity.InfinityCategories.F1B
