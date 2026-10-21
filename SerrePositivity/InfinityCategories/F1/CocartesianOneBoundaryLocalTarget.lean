module

public import SerrePositivity.InfinityCategories.F1.CocartesianOneBoundaryLocalSource
public import SerrePositivity.InfinityCategories.F1.UniverseOverFunctor

/-!
概要：一単体の全局所比較を境界へ制限した積表示は、同じ両端への直接制限の対。
方針：同じ target 積分解の射影と反変図式の合成則を計算する。
規約：元の標準単体上の分類比較を保持する。
使われ方：境界比較とセル比較の指定自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {C : Type u} [Category.{u} C] (i : Fin 2)
  (σ : (Δ[1] : SSet.{u}) ⟶ nerve C) (p q : CocartesianFibrationCategory (nerve C))
local notation "P" => cocartesianStrictTransportCoherentDiagram p.val.hom
local notation "Q" => cocartesianStrictTransportCoherentDiagram q.val.hom
local notation "T" => Functor.op (uliftOverFunctor (nerve C)) ⋙ intervalDiagramOverFunctor P Q
local notation "S" => cocartesianStandardSimplexHomComparison σ p q

/-- 元のセル比較を面側の端点へ直接制限する。 -/
def cocartesianOneBoundaryLocalTargetFace := S ≫ (T).map (faceSimplexOverMap 0 i σ).op

/-- 元のセル比較をホーン側の端点へ直接制限する。 -/
def cocartesianOneBoundaryLocalTargetHorn := S ≫ (T).map (hornSimplexOverMap 0 i σ).op

/-- 同じ境界へのセル作用の積表示は、同じ二端点の直接制限の対。 -/
lemma cocartesianOneBoundaryHomComparison_localTargetProduct :
    (S ≫ (T).map (boundarySimplexOverMap 0 σ).op) ≫
      (cocartesianOneBoundaryIntervalProductIso i σ P Q).hom =
    lift (cocartesianOneBoundaryLocalTargetFace i σ p q)
      (cocartesianOneBoundaryLocalTargetHorn i σ p q) := by
  apply CartesianMonoidalCategory.hom_ext
  · have h := congrArg (fun k ↦ (S ≫ (T).map (boundarySimplexOverMap 0 σ).op) ≫ k)
      (cocartesianOneBoundaryIntervalProductIso_hom_fst i σ P Q)
    have hr : (T).map (boundarySimplexOverMap 0 σ).op ≫ intervalDiagramOverPre P Q
        (uliftOverMorphism (HornBoundaryOver.faceInclusion 0 i σ)) =
        (T).map (faceSimplexOverMap 0 i σ).op := by
      change (T).map _ ≫ (T).map _ = _
      rw [← (T).map_comp]
      exact congrArg (fun f : HornBoundaryOver.face 0 i σ ⟶ Over.mk σ ↦ (T).map f.op)
        (faceSimplexOverMap_comp 0 i σ)
    have he := congrArg (fun k ↦ S ≫ k) hr
    have hp := (lift_fst (cocartesianOneBoundaryLocalTargetFace i σ p q)
      (cocartesianOneBoundaryLocalTargetHorn i σ p q)).symm
    simpa only [Category.assoc, cocartesianOneBoundaryLocalTargetFace,
      cocartesianOneBoundaryLocalTargetHorn, Functor.comp_obj, Functor.comp_map,
      Functor.op_obj, Functor.op_map, uliftOverFunctor, Over.mk_hom,
      intervalDiagramOverFunctor] using
      (h.trans ((Category.assoc _ _ _).trans he)).trans hp
  · have h := congrArg (fun k ↦ (S ≫ (T).map (boundarySimplexOverMap 0 σ).op) ≫ k)
      (cocartesianOneBoundaryIntervalProductIso_hom_snd i σ P Q)
    have hr : (T).map (boundarySimplexOverMap 0 σ).op ≫ intervalDiagramOverPre P Q
        (uliftOverMorphism (HornBoundaryOver.hornInclusion 0 i σ)) =
        (T).map (hornSimplexOverMap 0 i σ).op := by
      change (T).map _ ≫ (T).map _ = _
      rw [← (T).map_comp]
      exact congrArg (fun f : HornBoundaryOver.horn 0 i σ ⟶ Over.mk σ ↦ (T).map f.op)
        (hornSimplexOverMap_comp 0 i σ)
    have he := congrArg (fun k ↦ S ≫ k) hr
    have hp := (lift_snd (cocartesianOneBoundaryLocalTargetFace i σ p q)
      (cocartesianOneBoundaryLocalTargetHorn i σ p q)).symm
    simpa only [Category.assoc, cocartesianOneBoundaryLocalTargetFace,
      cocartesianOneBoundaryLocalTargetHorn, Functor.comp_obj, Functor.comp_map,
      Functor.op_obj, Functor.op_map, uliftOverFunctor, Over.mk_hom,
      intervalDiagramOverFunctor] using
      (h.trans ((Category.assoc _ _ _).trans he)).trans hp

end SerrePositivity.InfinityCategories
