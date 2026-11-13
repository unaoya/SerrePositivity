module
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.StrictSimplicialOrdinaryMap
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFMap
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBoundaryKanFunctor

/-! # 実 BF 段の前向き弱比較の通常 dg 射に関する厳密自然性
概要：同じ境界 Kan 値と実 BF 段の比較は、元の通常 dg 射にも厳密に自然。
方針：全 Hom 自然性を単位パラメータに制限し、同じ元の通常射を回収する。
規約：弱比較の逆は使わない。使われ方：新しい実 BF 射の Morita 不変性。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 境界の通常射の回収は、元の同じ境界商の Ex∞ 射と一致する。 -/
lemma presentedPerfectDGBFBoundaryOrdinaryMap (r : ℕ)
    {X Y : PerfDGInput.{u, v} A} (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialOrdinaryMap (presentedPerfectDGBFBoundaryFunctor A r) f =
      (show (presentedPerfectDGBFBoundaryFunctor A r).obj X ⟶
        (presentedPerfectDGBFBoundaryFunctor A r).obj Y from
          (presentedPerfectDGBoundaryKanMap A r f).hom) := by
  apply (eHomEquiv SSet).injective
  exact (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialOrdinaryMap_hom _ f).trans
    (presentedPerfectDGBoundaryKanEnrichedFunctor_hom A r f)

/-- 元の前向き段比較は、同じ境界 Kan 射と実段射に関して厳密に自然。 -/
lemma presentedPerfectDGBFStageComparison_naturality (r : ℕ)
    (S : PresentedPerfectDGBFStage.{u, v} A r) {X Y : PerfDGInput.{u, v} A} (f : X ⟶ Y) :
    (show ((presentedPerfectDGBFBoundaryFunctor A r).obj X).obj ⟶
      ((presentedPerfectDGBFBoundaryFunctor A r).obj Y).obj from
        (presentedPerfectDGBoundaryKanMap A r f).hom) ≫
        (show ((presentedPerfectDGBFBoundaryFunctor A r).obj Y).obj ⟶
          (S.functor.obj Y).obj from S.comparison Y) =
      (show ((presentedPerfectDGBFBoundaryFunctor A r).obj X).obj ⟶
        (S.functor.obj X).obj from S.comparison X) ≫
        (show (S.functor.obj X).obj ⟶ (S.functor.obj Y).obj from
          _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialOrdinaryMap S.functor f) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialOrdinaryMap_naturality
    (presentedPerfectDGBFBoundaryFunctor A r) S.functor S.comparison S.naturality f
  rw [presentedPerfectDGBFBoundaryOrdinaryMap A r f] at h
  exact h

/-- 正の BF 段の実射は、その段の元の厳密豊穣作用による通常射そのもの。 -/
lemma presentedPerfectDGBFMap_positive_app {X Y : PerfDGInput.{u, v} A}
    (f : X ⟶ Y) (r : ℕ) :
    (presentedPerfectDGBFMap A f).app (r + 1) =
      (show (((presentedPerfectDGBFPositiveStage A r).functor).obj X).obj ⟶
        (((presentedPerfectDGBFPositiveStage A r).functor).obj Y).obj from
          _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialOrdinaryMap (presentedPerfectDGBFPositiveStage A r).functor f) :=
  presentedPerfectDGBFMap_app A f (r + 1)

/-- 零段の同じ実 BF 射は、元の境界 Kan 射の loop を厳密に回収する。 -/
lemma presentedPerfectDGBFMap_zero_app {X Y : PerfDGInput.{u, v} A} (f : X ⟶ Y) :
    (presentedPerfectDGBFMap A f).app 0 =
      (PointedObject.basedHomFunctor PointedSimplicialSet.circle.{max (u + 1) v}).map
        (presentedPerfectDGBoundaryKanMap A 0 f).hom := by
  have h := presentedPerfectDGBFMap_app A f 0
  refine h.trans ?_
  change _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialOrdinaryMap
    ((presentedPerfectDGBFBoundaryFunctor A 0).comp SSet pointedStandardLoopEnrichedFunctor) f = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialOrdinaryMap_comp, presentedPerfectDGBFBoundaryOrdinaryMap A 0 f]
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialOrdinaryMap_of_hom pointedStandardLoopEnrichedFunctor _
    (pointedStandardLoopMap
      (show (presentedPerfectDGBFBoundaryFunctor A 0).obj X ⟶
        (presentedPerfectDGBFBoundaryFunctor A 0).obj Y from
          (presentedPerfectDGBoundaryKanMap A 0 f).hom))
    (pointedStandardLoopEnrichedFunctor_hom _)

end SerrePositivity.KST.SConstruction
