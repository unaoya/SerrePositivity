module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.HornBoundaryFibers
public import SerrePositivity.InfinityCategories.F1.Cocartesian.CellAttachmentFibrations

/-!
概要：標準境界のホーンへの制限と欠けた面の境界制限は、両側で Kan fibration。
方針：同じ四つの標準包含の単射性を、元の native core と区間 Hom の制限へ移す。
規約：実際の指定ホーン値の延長空間も Kan と証明する。
使われ方：境界比較の帰納の fiber 判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {B : SSet.{u}} (n : ℕ) (i : Fin (n + 2)) (σ : (Δ[n + 1] : SSet.{u}) ⟶ B)

section Source
variable {E F : SSet.{u}} [Quasicategory B]
  (p : E ⟶ B) [CocartesianFibration p] (q : F ⟶ B) [CocartesianFibration q]

/-- 同じ標準境界からホーンへの native core 制限は Kan fibration。 -/
lemma cocartesianHornBoundary_nativeRestriction_fibration :
    Fibration (cocartesianPullbackNativeLiftPre p q (HornBoundaryOver.hornInclusion n i σ)) :=
  cocartesianPullbackNativeLiftPre_fibration p q (HornBoundaryOver.hornInclusion n i σ)

/-- 同じ欠けた標準面から共有境界への native core 制限は Kan fibration。 -/
lemma cocartesianHornBoundary_nativeFaceRestriction_fibration :
    Fibration (cocartesianPullbackNativeLiftPre p q (HornBoundaryOver.toFace n i σ)) :=
  cocartesianPullbackNativeLiftPre_fibration p q (HornBoundaryOver.toFace n i σ)

/-- 元のホーン上の指定 native Hom を境界へ延長する実際の空間は Kan。 -/
lemma cocartesianHornBoundary_nativeExtension_kanComplex
    (r : ((SSet.uliftFunctor.{u + 1, u}).obj
      ((cocartesianPullbackNativeCoreFunctor p q).obj
        (Opposite.op (HornBoundaryOver.horn n i σ)))) _⦋0⦌) :
    KanComplex (vertexFiber
      (cocartesianPullbackNativeLiftPre p q (HornBoundaryOver.hornInclusion n i σ)) r) := by
  letI := cocartesianHornBoundary_nativeRestriction_fibration n i σ p q
  exact vertexFiber_kanComplex_of_leftFibration _ _
end Source

section Target
variable {X : SSet.{u + 1}} [Quasicategory X]
  (P Q : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ X)

/-- 分類先の同じ標準境界からホーンへの制限も Kan fibration。 -/
lemma cocartesianHornBoundary_intervalRestriction_fibration :
    Fibration (intervalDiagramOverPre P Q
      (uliftOverMorphism (HornBoundaryOver.hornInclusion n i σ))) :=
  cocartesianCellAttachment_intervalRestriction_fibration
    (HornBoundaryOver.toFace n i σ) (HornBoundaryOver.toHorn n i σ)
    (HornBoundaryOver.faceInclusion n i σ) (HornBoundaryOver.hornInclusion n i σ)
    (HornBoundaryOver.isPushout n i σ) P Q

/-- 分類先の同じ欠けた面から共有境界への制限も Kan fibration。 -/
lemma cocartesianHornBoundary_intervalFaceRestriction_fibration :
    Fibration (intervalDiagramOverPre P Q (uliftOverMorphism (HornBoundaryOver.toFace n i σ))) := by
  letI : Mono (uliftOverMorphism.{u, u + 1} (HornBoundaryOver.toFace n i σ)).left :=
    SimplicialModel.UniverseLift.mono_map (HornBoundaryOver.toFace n i σ).left
  exact intervalDiagramOverPre_fibration P Q _

/-- 分類先のホーン上の指定 Hom を境界へ延長する実際の空間も Kan。 -/
lemma cocartesianHornBoundary_intervalExtension_kanComplex
    (r : ((intervalDiagramOverFunctor P Q).obj (Opposite.op
      (Over.mk ((SSet.uliftFunctor.{u + 1, u}).map (HornBoundaryOver.horn n i σ).hom)))) _⦋0⦌) :
    KanComplex (vertexFiber (intervalDiagramOverPre P Q
      (uliftOverMorphism (HornBoundaryOver.hornInclusion n i σ))) r) := by
  letI := cocartesianHornBoundary_intervalRestriction_fibration n i σ P Q
  exact vertexFiber_kanComplex_of_leftFibration _ _
end Target

end SerrePositivity.InfinityCategories
