module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.HornBoundaryHomPullbacks
public import SerrePositivity.InfinityCategories.F1.Cocartesian.CellAttachmentFibers

/-!
概要：ホーン上の同じ Hom を固定した境界全体への延長を、欠けた面の境界固定 fiber と同定する。
方針：元の四射の同じ pushout に、セル延長の射影を保つ fiber 同型を適用する。
規約：元の指定 Hom と面への直接制限を保持する。
使われ方：境界全体の比較を低次元の境界固定比較から作る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {B : SSet.{u}} (n : ℕ) (i : Fin (n + 2)) (σ : (Δ[n + 1] : SSet.{u}) ⟶ B)

section Source
variable {E F : SSet.{u}} [Quasicategory B]
  (p : E ⟶ B) [CocartesianFibration p] (q : F ⟶ B) [CocartesianFibration q]
  (r : ((SSet.uliftFunctor.{u + 1, u}).obj
    ((cocartesianPullbackNativeCoreFunctor p q).obj
      (Opposite.op (HornBoundaryOver.horn n i σ)))) _⦋0⦌)

/-- 同じホーン上の指定 native Hom の境界延長空間は、欠けた面の境界固定 fiber。 -/
def cocartesianHornBoundary_nativeExtensionFiberIso :
    vertexFiber (cocartesianPullbackNativeLiftPre p q (HornBoundaryOver.hornInclusion n i σ)) r ≅
    vertexFiber (cocartesianPullbackNativeLiftPre p q (HornBoundaryOver.toFace n i σ))
      ((cocartesianPullbackNativeLiftPre p q (HornBoundaryOver.toHorn n i σ)).app
        (Opposite.op ⦋0⦌) r) :=
  cocartesianCellAttachment_sourceExtensionFiberIso
    (HornBoundaryOver.toFace n i σ) (HornBoundaryOver.toHorn n i σ)
    (HornBoundaryOver.faceInclusion n i σ) (HornBoundaryOver.hornInclusion n i σ)
    (HornBoundaryOver.isPushout n i σ) p q r

/-- 同じ native fiber 同型は、元の欠けた面への直接制限を保つ。 -/
lemma cocartesianHornBoundary_nativeExtensionFiberIso_hom_ι :
    (cocartesianHornBoundary_nativeExtensionFiberIso n i σ p q r).hom ≫
      vertexFiberι (cocartesianPullbackNativeLiftPre p q (HornBoundaryOver.toFace n i σ))
        ((cocartesianPullbackNativeLiftPre p q (HornBoundaryOver.toHorn n i σ)).app
          (Opposite.op ⦋0⦌) r) =
    vertexFiberι (cocartesianPullbackNativeLiftPre p q (HornBoundaryOver.hornInclusion n i σ)) r ≫
      cocartesianPullbackNativeLiftPre p q (HornBoundaryOver.faceInclusion n i σ) :=
  vertexFiberIsoOfIsPullback_hom_ι (cocartesianHornBoundary_native_isPullback n i σ p q) r
end Source

section Target
variable {X : SSet.{u + 1}} (P Q : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ X)
  (r : ((intervalDiagramOverFunctor P Q).obj (Opposite.op
    (Over.mk ((SSet.uliftFunctor.{u + 1, u}).map (HornBoundaryOver.horn n i σ).hom)))) _⦋0⦌)

/-- 同じホーン上の指定 target Hom の境界延長空間も、欠けた面の境界固定 fiber。 -/
def cocartesianHornBoundary_intervalExtensionFiberIso :
    vertexFiber (intervalDiagramOverPre P Q
      (uliftOverMorphism (HornBoundaryOver.hornInclusion n i σ))) r ≅
    vertexFiber (intervalDiagramOverPre P Q (uliftOverMorphism (HornBoundaryOver.toFace n i σ)))
      ((intervalDiagramOverPre P Q (uliftOverMorphism (HornBoundaryOver.toHorn n i σ))).app
        (Opposite.op ⦋0⦌) r) :=
  vertexFiberIsoOfIsPullback (cocartesianHornBoundary_interval_isPullback n i σ P Q) r

/-- 同じ target fiber 同型も、元の欠けた面への直接制限を保つ。 -/
lemma cocartesianHornBoundary_intervalExtensionFiberIso_hom_ι :
    (cocartesianHornBoundary_intervalExtensionFiberIso n i σ P Q r).hom ≫
      vertexFiberι (intervalDiagramOverPre P Q (uliftOverMorphism (HornBoundaryOver.toFace n i σ)))
        ((intervalDiagramOverPre P Q (uliftOverMorphism (HornBoundaryOver.toHorn n i σ))).app
          (Opposite.op ⦋0⦌) r) =
    vertexFiberι (intervalDiagramOverPre P Q
      (uliftOverMorphism (HornBoundaryOver.hornInclusion n i σ))) r ≫
      intervalDiagramOverPre P Q (uliftOverMorphism (HornBoundaryOver.faceInclusion n i σ)) :=
  vertexFiberIsoOfIsPullback_hom_ι (cocartesianHornBoundary_interval_isPullback n i σ P Q) r
end Target

end SerrePositivity.InfinityCategories
