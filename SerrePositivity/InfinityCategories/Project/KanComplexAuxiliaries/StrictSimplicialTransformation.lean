module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import Mathlib.AlgebraicTopology.SimplicialCategory.Basic
public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic

/-! # 全 Hom の可換性からの厳密単体的自然変換
概要：通常成分と全単体の前後合成の可換性を、単位次数の豊穣自然変換へ束ねる。
方針：単位の単体を評価し、後合成は豊穣関手の全合成保存で移す。
規約：頂点だけの自然性には制限しない。使われ方：同じ S₁ 比較と Kan 後の比較。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet

/-- 全 Hom の前後合成で可換な通常成分を、厳密な単体的自然変換へ束ねる。 -/
def strictSimplicialTransformationOfWhisker
    {C : Type v} {D : Type w} [Category.{u} C] [Category.{u} D]
    [SimplicialCategory C] [SimplicialCategory D]
    (F G : EnrichedFunctor SSet.{u} C D) (τ : ∀ X, F.obj X ⟶ G.obj X)
    (h : ∀ X Y, F.map X Y ≫ eHomWhiskerLeft SSet (F.obj X) (τ Y) =
      G.map X Y ≫ eHomWhiskerRight SSet (τ X) (G.obj Y)) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F G where
  app X := eHomEquiv SSet (τ X)
  naturality X Y := by
    ext n t
    exact types_congr_hom (NatTrans.congr_app (h X Y) n) t.2

/-- 厳密な単体的自然変換は、任意の厳密豊穣関手で後合成できる。 -/
def strictSimplicialTransformationPostcompose
    {C : Type v} {D : Type w} {E : Type z}
    [EnrichedCategory SSet.{u} C] [EnrichedCategory SSet.{u} D]
    [EnrichedCategory SSet.{u} E]
    (F G : EnrichedFunctor SSet.{u} C D) (H : EnrichedFunctor SSet.{u} D E)
    (τ : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F G) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u}))
      (F.comp SSet H) (G.comp SSet H) where
  app X := τ.app X ≫ H.map _ _
  naturality X Y := by
    ext n t
    have h := types_congr_hom (NatTrans.congr_app (τ.naturality X Y) n) t
    have hf := types_congr_hom (NatTrans.congr_app
      (H.map_comp (F.obj X) (F.obj Y) (G.obj Y)) n)
      ((F.map X Y).app n t.2, (τ.app Y).app n t.1)
    have hg := types_congr_hom (NatTrans.congr_app
      (H.map_comp (F.obj X) (G.obj X) (G.obj Y)) n)
      ((τ.app X).app n t.1, (G.map X Y).app n t.2)
    exact hf.symm.trans ((congrArg (fun x => (H.map (F.obj X) (G.obj Y)).app n x) h).trans hg)

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationOfWhisker (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.strictSimplicialTransformationOfWhisker := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationOfWhisker

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationPostcompose (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.strictSimplicialTransformationPostcompose := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationPostcompose

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.strictSimplicialTransformationOfWhisker._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationOfWhisker._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.strictSimplicialTransformationPostcompose._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationPostcompose._proof_1
