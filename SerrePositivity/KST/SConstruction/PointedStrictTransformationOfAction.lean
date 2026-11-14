module
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.StrictSimplicialTransformation
public import SerrePositivity.KST.SConstruction.PointedSSetWhisker

/-! # 全実作用の可換性からの標準点つき厳密自然変換
概要：同じ全 basedHom 族の評価の可換性を、厳密豊穣自然変換へ束ねる。
方針：包含と uncurry の単射性で全 Hom の前後合成の等号を検出する。
規約：通常射だけの自然性は仮定にしない。使われ方：Ex∞ の suspension 比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet

/-- 全 Hom の評価の可換性は、標準点つき豊穣の前後合成の可換性を与える。 -/
lemma pointedStrictTransformationOfAction_whisker
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (F G : EnrichedFunctor SSet.{u} C PointedSSetObject.{u})
    (τ : ∀ X, F.obj X ⟶ G.obj X)
    (h : ∀ X Y, ((show (F.obj X).obj ⟶ (G.obj X).obj from τ X).right ▷
        (X ⟶[SSet.{u}] Y)) ≫
        uncurry (G.map X Y ≫ PointedObject.basedHomι (G.obj X).obj (G.obj Y).obj) =
      uncurry (F.map X Y ≫ PointedObject.basedHomι (F.obj X).obj (F.obj Y).obj) ≫
        (show (F.obj Y).obj ⟶ (G.obj Y).obj from τ Y).right) (X Y : C) :
    F.map X Y ≫ eHomWhiskerLeft SSet (F.obj X) (τ Y) =
      G.map X Y ≫ eHomWhiskerRight SSet (τ X) (G.obj Y) := by
  rw [pointedSSetObject_whiskerLeft, pointedSSetObject_whiskerRight]
  apply (cancel_mono (PointedObject.basedHomι (F.obj X).obj (G.obj Y).obj)).mp
  apply uncurry_injective
  erw [Category.assoc,
    pointedFamilyPost_evaluation (F.obj X).obj (F.obj Y).obj (G.obj Y).obj
      (F.map X Y) (τ Y),
    pointedFamily_pre_evaluation (τ X) (G.obj Y).obj (G.map X Y)]
  exact (h X Y).symm

/-- 全 Hom の実作用に自然な点つき成分は、標準の厳密豊穣自然変換を与える。 -/
def pointedStrictTransformationOfAction
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (F G : EnrichedFunctor SSet.{u} C PointedSSetObject.{u})
    (τ : ∀ X, F.obj X ⟶ G.obj X)
    (h : ∀ X Y, ((show (F.obj X).obj ⟶ (G.obj X).obj from τ X).right ▷
        (X ⟶[SSet.{u}] Y)) ≫
        uncurry (G.map X Y ≫ PointedObject.basedHomι (G.obj X).obj (G.obj Y).obj) =
      uncurry (F.map X Y ≫ PointedObject.basedHomι (F.obj X).obj (F.obj Y).obj) ≫
        (show (F.obj Y).obj ⟶ (G.obj Y).obj from τ Y).right) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F G :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationOfWhisker F G τ
    (pointedStrictTransformationOfAction_whisker F G τ h)

end SerrePositivity.KST.SConstruction
