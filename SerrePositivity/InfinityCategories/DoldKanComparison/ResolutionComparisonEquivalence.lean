module

public import SerrePositivity.InfinityCategories.DoldKanComparison.PrecompositionHomotopyDescent

/-!
# Kan 標的の解像の標準比較射の実際のホモトピー逆

概要：任意の Kan 複体から解像の右随伴への標準比較射は単体的ホモトピー同値である。
方針：右随伴の対象上の解像の余単位を射影に沿って降下し、転置と反映で両合成を計算する。
規約：右随伴の対象自体の Kan 性は追加の前提にしない。
使われ方：HA 1.3.1.17、Kerodon Theorem 4.6.7.5 の写像空間の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.DoldKanComparison
open CategoryTheory MonoidalClosed SSet

/-- 概要：標準比較射の解像での像の後の余単位は元の解像の射影である。
方針：標準比較射が射影の随伴転置であることと随伴対応の逆性を使う。
規約：単体集合 K は任意。
使われ方：Kerodon Theorem 4.6.7.5 の比較射の片方の合成の計算。 -/
lemma resolutionComparison_counit (K : SSet.{u}) :
    coherentResolution.map (coherentResolutionComparison K) ≫
      coherentResolutionAdjunction.counit.app K = coherentResolutionProjectionAll.app K := by
  calc
    _ = (coherentResolutionAdjunction.homEquiv K K).symm
        (coherentResolutionComparison K) :=
      (coherentResolutionAdjunction.homEquiv_counit K K (coherentResolutionComparison K)).symm
    _ = _ := by
      change (coherentResolutionAdjunction.homEquiv K K).symm
        ((coherentResolutionAdjunction.homEquiv K K) (coherentResolutionProjectionAll.app K)) = _
      exact (coherentResolutionAdjunction.homEquiv K K).symm_apply_apply _

/-- 概要：任意の Kan 複体への解像の標準比較射は実際の単体的ホモトピー逆を持つ。
方針：余単位を解像の射影に沿って降下し、一方の合成はホモトピーを随伴転置し、他方は反映する。
規約：射影の一般の同値性は F1 の確定済みのセル帰納法を使い、引用は追加しない。
使われ方：HA 1.3.1.17 の実際の dg nerve 比較の充満忠実性。 -/
lemma resolutionComparison_homotopyEquivalence (K : SSet.{u}) [KanComplex K] :
    IsSimplicialHomotopyEquivalence (coherentResolutionComparison K) := by
  obtain ⟨g, ⟨H⟩⟩ := precomposition_exists_homotopy
    (A := coherentResolution.obj (coherentResolutionRightAdjoint.obj K))
    (B := coherentResolutionRightAdjoint.obj K) (K := K)
    (coherentResolutionProjectionAll.app (coherentResolutionRightAdjoint.obj K))
    (coherentResolutionProjectionAll_isPrecompositionEquivalence _)
    (coherentResolutionAdjunction.counit.app K)
  refine ⟨g, ?_, ?_⟩
  · let e := (functorIsoOfSimplicialHomotopy H).precomp
      (coherentResolution.map (coherentResolutionComparison K))
    have hn : coherentResolution.map (coherentResolutionComparison K) ≫
        coherentResolutionProjectionAll.app (coherentResolutionRightAdjoint.obj K) =
          coherentResolutionProjectionAll.app K ≫ coherentResolutionComparison K :=
      coherentResolutionProjectionAll.naturality (coherentResolutionComparison K)
    have hl : coherentResolution.map (coherentResolutionComparison K) ≫
        (coherentResolutionProjectionAll.app (coherentResolutionRightAdjoint.obj K) ≫ g) =
          coherentResolutionProjectionAll.app K ≫ (coherentResolutionComparison K ≫ g) := by
      rw [← Category.assoc, hn, Category.assoc]
    have hL := e.simplicialHomotopy
    rw [hl, resolutionComparison_counit] at hL
    have hL' : SSet.Homotopy
        (coherentResolutionProjectionAll.app K ≫ (coherentResolutionComparison K ≫ g))
        (coherentResolutionProjectionAll.app K ≫ 𝟙 K) := by
      have hi : (coherentResolutionProjectionAll.app K : coherentResolution.obj K ⟶ K) ≫
          (𝟙 K) = coherentResolutionProjectionAll.app K := Category.comp_id _
      rw [hi]
      exact hL
    exact precomposition_reflect_homotopy (coherentResolutionProjectionAll.app K)
      (coherentResolutionProjectionAll_isPrecompositionEquivalence K) hL'
  · have hR := resolutionHomotopyTranspose H
    rw [resolutionHomEquiv_projection_comp, resolutionHomEquiv_counit] at hR
    exact ⟨hR⟩

end SerrePositivity.InfinityCategories.DoldKanComparison
