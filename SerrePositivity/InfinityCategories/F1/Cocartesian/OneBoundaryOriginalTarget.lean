module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.OneBoundaryOriginalSource

/-!
概要：元の大域分類作用を一次元境界へ制限した積表示は、同じ両端への直接制限の対。
方針：同じ target 積分解の射影と、底上の直接制限の厳密な自然性を計算する。
規約：元の分類図式を選び直さない。
使われ方：一次元境界比較の元の大域作用との指定同型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {C : Type u} [Category.{u} C] (i : Fin 2) (σ : (Δ[1] : SSet.{u}) ⟶ nerve C)
  (p q : CocartesianFibrationCategory (nerve C))
local notation "P" => cocartesianStrictTransportCoherentDiagram p.val.hom
local notation "Q" => cocartesianStrictTransportCoherentDiagram q.val.hom

/-- 元の大域作用を面側の同じ端点へ直接制限する。 -/
def cocartesianOneBoundaryOriginalFaceAction :=
  cocartesianStraighteningHomInterval p q ≫ intervalDiagramRestriction
    ((SSet.uliftFunctor.{u + 1, u}).map (HornBoundaryOver.face 0 i σ).hom) P Q

/-- 元の大域作用をホーン側の同じ端点へ直接制限する。 -/
def cocartesianOneBoundaryOriginalHornAction :=
  cocartesianStraighteningHomInterval p q ≫ intervalDiagramRestriction
    ((SSet.uliftFunctor.{u + 1, u}).map (HornBoundaryOver.horn 0 i σ).hom) P Q

/-- 元の全 Hom 上で、同じ境界への大域作用の積表示は両端の直接制限の対。 -/
lemma cocartesianOneBoundaryHomComparison_originalTargetProduct :
    (cocartesianStraighteningHomInterval p q ≫
      intervalDiagramRestriction
        ((SSet.uliftFunctor.{u + 1, u}).map (HornBoundaryOver.apex 0 σ).hom) P Q) ≫
      (cocartesianOneBoundaryIntervalProductIso i σ P Q).hom =
    lift (cocartesianOneBoundaryOriginalFaceAction i σ p q)
      (cocartesianOneBoundaryOriginalHornAction i σ p q) := by
  let T := cocartesianStraighteningHomInterval p q ≫ intervalDiagramRestriction
    ((SSet.uliftFunctor.{u + 1, u}).map (HornBoundaryOver.apex 0 σ).hom) P Q
  apply CartesianMonoidalCategory.hom_ext
  · have h := congrArg (fun k ↦ T ≫ k)
      (cocartesianOneBoundaryIntervalProductIso_hom_fst i σ P Q)
    have hr := intervalDiagramOverPre_restriction P Q
      (uliftOverMorphism (HornBoundaryOver.faceInclusion 0 i σ))
    have he := congrArg (fun k ↦ cocartesianStraighteningHomInterval p q ≫ k) hr
    have hp := (lift_fst (cocartesianOneBoundaryOriginalFaceAction i σ p q)
      (cocartesianOneBoundaryOriginalHornAction i σ p q)).symm
    simpa only [T, Category.assoc, cocartesianOneBoundaryOriginalFaceAction,
      cocartesianOneBoundaryOriginalHornAction, Over.mk_hom, intervalDiagramOverFunctor] using
      (h.trans ((Category.assoc _ _ _).trans he)).trans hp
  · have h := congrArg (fun k ↦ T ≫ k)
      (cocartesianOneBoundaryIntervalProductIso_hom_snd i σ P Q)
    have hr := intervalDiagramOverPre_restriction P Q
      (uliftOverMorphism (HornBoundaryOver.hornInclusion 0 i σ))
    have he := congrArg (fun k ↦ cocartesianStraighteningHomInterval p q ≫ k) hr
    have hp := (lift_snd (cocartesianOneBoundaryOriginalFaceAction i σ p q)
      (cocartesianOneBoundaryOriginalHornAction i σ p q)).symm
    simpa only [T, Category.assoc, cocartesianOneBoundaryOriginalFaceAction,
      cocartesianOneBoundaryOriginalHornAction, Over.mk_hom, intervalDiagramOverFunctor] using
      (h.trans ((Category.assoc _ _ _).trans he)).trans hp

end SerrePositivity.InfinityCategories
