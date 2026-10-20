module

public import SerrePositivity.InfinityCategories.F1.UnstraighteningSourceRestrictionEquivalence
public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningBaseChange
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorOverIsoUncurry

/-!
概要：図式制限が充満忠実なら、元の unstraightening 間の相対 Hom の引き戻し作用も同値。
方針：実際の引き戻しを制限後の unstraightening と同型で移し、c1 の始域制限へ厳密に戻す。
規約：底変換の図式の同型と、元の relativeFunctorPullback 自体を保持する。
使われ方：初頂点の局所化に沿う left fibration の引き戻しの充満忠実性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

local instance {E B D : SSet.{u + 1}} (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
    LeftFibration (pullback.snd p k) :=
  ⟨leftFibrations.pullback_snd p k (LeftFibration.mem (p := p))⟩

/-- 引き戻した二つの全空間の相対 Hom を、制限後の二つの unstraightening へ厳密に移す。 -/
def leftUnstraighteningPullbackRelativeIso {B D : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (k : D ⟶ B) :
    relativeFunctorSpace (pullback.snd (leftUnstraighteningProjection G) k)
      (pullback.snd (leftUnstraighteningProjection F) k) ≅
    relativeFunctorSpace (leftUnstraighteningProjection (k ≫ G))
      (leftUnstraighteningProjection (k ≫ F)) :=
  relativeFunctorOverIso (leftUnstraighteningBaseChangeOverIso F k).symm
    (leftUnstraighteningBaseChangeOverIso G k).symm

/-- 同型の逆を元の全空間へ写すと、標準引き戻しの第一射影を回収する。 -/
lemma leftUnstraighteningBaseChangeIso_inv_map {B D : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (k : D ⟶ B) :
    (leftUnstraighteningBaseChangeIso F k).inv ≫ leftUnstraighteningMap (k ≫ F) F k rfl =
      pullback.fst (leftUnstraighteningProjection F) k :=
  (leftUnstraighteningMap_isPullback (k ≫ F) F k rfl).isoPullback_inv_fst

/-- 実際の引き戻しの相対 Hom 作用は、同じ始域制限を底変換の同型で移したもの。 -/
lemma leftUnstraighteningPullbackRelativeIso_post_compare {B D : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (k : D ⟶ B) :
    relativeFunctorPullback (leftUnstraighteningProjection F) (leftUnstraighteningProjection G) k ≫
      (leftUnstraighteningPullbackRelativeIso F G k).hom ≫
      relativeFunctorSquarePost (leftUnstraighteningProjection (k ≫ G))
        (leftUnstraighteningProjection G) k (leftUnstraighteningMap (k ≫ G) G k rfl)
        (leftUnstraighteningMap_projection (k ≫ G) G k rfl)
        (leftUnstraighteningProjection (k ≫ F)) =
    relativeFunctorOverPre (leftUnstraighteningProjection G)
      (leftUnstraighteningOverBaseMap F k) := by
  apply relativeFunctorUncurry_injective
  rw [← Category.assoc, relativeFunctorSquarePost_uncurry,
    leftUnstraighteningPullbackRelativeIso]
  have hi := relativeFunctorOverIso_uncurry
    (leftUnstraighteningBaseChangeOverIso F k).symm
    (leftUnstraighteningBaseChangeOverIso G k).symm
    (relativeFunctorPullback (leftUnstraighteningProjection F)
      (leftUnstraighteningProjection G) k)
  refine (congrArg (fun t ↦ t ≫ leftUnstraighteningMap (k ≫ G) G k rfl) hi).trans ?_
  have hr := relativeFunctorOverPre_uncurry (leftUnstraighteningProjection G)
    (leftUnstraighteningOverBaseMap F k) (𝟙 _)
  simp only [Category.id_comp] at hr
  rw [hr]
  change (((leftUnstraighteningBaseChangeIso F k).hom ▷ _) ≫
    relativeFunctorUncurry (relativeFunctorPullback
      (leftUnstraighteningProjection F) (leftUnstraighteningProjection G) k) ≫
    (leftUnstraighteningBaseChangeIso G k).inv) ≫
      leftUnstraighteningMap (k ≫ G) G k rfl = _
  simp only [Category.assoc]
  rw [leftUnstraighteningBaseChangeIso_inv_map]
  have hu := relativeFunctorPullback_uncurry_fst (leftUnstraighteningProjection F)
    (leftUnstraighteningProjection G) k (𝟙 _)
  simp only [Category.id_comp] at hu
  rw [hu]
  rw [← Category.assoc, ← comp_whiskerRight, leftUnstraighteningBaseChangeIso_hom_fst]
  rfl

/-- 図式の充満忠実な制限は、元の unstraightening の実際の引き戻し作用も同値にする。 -/
lemma leftUnstraighteningPullback_isQCatEquivalence
    {B D : SSet.{u + 1}} (F G : B ⟶ SpaceInfinity.{u}) (k : D ⟶ B)
    (hk : IsFullyFaithful ((pre k).app SpaceInfinity.{u})) :
    IsQCatEquivalence
      (relativeFunctorPullback (leftUnstraighteningProjection F)
        (leftUnstraighteningProjection G) k) := by
  have h₁ := (qCatEquivalenceOfIso (leftUnstraighteningPullbackRelativeIso F G k)).isQCatEquivalence
  have h₂ := (qCatEquivalenceOfIso
    (relativeFunctorPullbackSquareIso (leftUnstraighteningProjection (k ≫ G))
      (leftUnstraighteningProjection G) k (leftUnstraighteningMap (k ≫ G) G k rfl)
      (leftUnstraighteningMap_isPullback (k ≫ G) G k rfl)
      (leftUnstraighteningProjection (k ≫ F)))).isQCatEquivalence
  have hc : IsQCatEquivalence
      (relativeFunctorPullback (leftUnstraighteningProjection F)
          (leftUnstraighteningProjection G) k ≫
        (leftUnstraighteningPullbackRelativeIso F G k).hom ≫
        relativeFunctorSquarePost (leftUnstraighteningProjection (k ≫ G))
          (leftUnstraighteningProjection G) k (leftUnstraighteningMap (k ≫ G) G k rfl)
          (leftUnstraighteningMap_projection (k ≫ G) G k rfl)
          (leftUnstraighteningProjection (k ≫ F))) := by
    rw [leftUnstraighteningPullbackRelativeIso_post_compare]
    exact leftUnstraighteningSourceRestriction_isQCatEquivalence F G k hk
  exact (h₁.comp h₂).cancel_right hc

/-- 初頂点局所化に沿う、元の coherent unstraightening 間の実際の相対 Hom 引き戻しは同値。 -/
lemma leftUnstraighteningFirstVertexPullback_isQCatEquivalence
    (B : SSet.{u})
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    IsQCatEquivalence
      (relativeFunctorPullback (leftUnstraighteningProjection F) (leftUnstraighteningProjection G)
        ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B))) :=
  leftUnstraighteningPullback_isQCatEquivalence F G _
    (localization_pre_isFullyFaithful
      (transportSimplexFirstVertexMap_ulift_isLocalization.{u, u + 1} B) SpaceInfinity.{u})

end SerrePositivity.InfinityCategories
