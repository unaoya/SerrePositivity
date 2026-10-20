module

public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialTotalEdgePrecomposition
public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialRestrictionHomSquare
public import SerrePositivity.InfinityCategories.HomotopyLimits.PointHomCospanIso

/-!
概要：同じ底上の制限関手の像に、実際の比較辺を前置する初期 Hom 間の写像。
方針：初期 Hom の後合成と相対前置を合成し、底の点図式の表示変更を照合する。
規約：既存の Hom 前合成と同じ底の切断を使う。使われ方：枝比較円柱の共通始対象への像。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {E F B : SSet.{u}} [Quasicategory B]
  (p : E ⟶ B) (q : F ⟶ B) [InnerFibration q]
  (r : E ⟶ F) (hr : r ≫ q = p) (d : E _⦋0⦌)
  {c : F _⦋0⦌} (e : F.Edge c (r.app (Opposite.op ⦋0⦌) d)) (y : B _⦋0⦌)
local notation "b" => ConcreteCategory.hom (NatTrans.app r (Opposite.op ⦋0⦌)) d
local notation "t" => SSet.yonedaEquiv.symm (SSet.Edge.edge e)
local notation "M" => leftFibrationInitialTotalMap p q r hr d b rfl y
local notation "hB" => leftFibrationInitialBaseDiagram_eq p q r hr d b rfl

/-- 制限関手による初期 Hom の像に、指定された同じ実際の比較辺を前置する。 -/
def initialRestrictionTotalPrecomposition :
    leftFibrationInitialTotal p d y ⟶ leftFibrationInitialTotal q c y :=
  M ≫ initialTotalEdgePrecomposition q e y

/-- 制限と前置は、元の終点評価の制限関手による像を厳密に保つ。 -/
lemma initialRestrictionTotalPrecomposition_evaluation :
    initialRestrictionTotalPrecomposition p q r hr d e y ≫
        leftFibrationInitialEvaluation q c y =
      leftFibrationInitialEvaluation p d y ≫ vertexFiberMap p q r hr y := by
  rw [initialRestrictionTotalPrecomposition, Category.assoc,
    initialTotalEdgePrecomposition_evaluation, leftFibrationInitialTotalMap_evaluation]

/-- 底の射影は、元の底の点図式から実際の比較辺によって前合成したもの。 -/
lemma initialRestrictionTotalPrecomposition_projection :
    initialRestrictionTotalPrecomposition p q r hr d e y ≫
        leftFibrationInitialProjection q c y =
      leftFibrationInitialProjection p d y ≫ cosliceEdgeFiberPrecomposition (t ≫ q)
        (SSet.yonedaEquiv.symm c ≫ q) (SSet.yonedaEquiv.symm d ≫ p)
        (initialTotalEdgeBase_source q e) (initialRestrictionEdgeBase_eq p q r hr d e).symm y := by
  let C := eqToHom (congrArg (fun z ↦ vertexFiber (sliceUnderProjection z) y) (hB).symm)
  let K := cosliceEdgeFiberPrecomposition (t ≫ q)
    (SSet.yonedaEquiv.symm c ≫ q) (SSet.yonedaEquiv.symm b ≫ q)
    (initialTotalEdgeBase_source q e) (initialTotalEdgeBase_target q e) y
  let K' := cosliceEdgeFiberPrecomposition (t ≫ q)
    (SSet.yonedaEquiv.symm c ≫ q) (SSet.yonedaEquiv.symm d ≫ p)
    (initialTotalEdgeBase_source q e) (initialRestrictionEdgeBase_eq p q r hr d e).symm y
  have hK : K = C ≫ K' := by
    have h := cosliceEdgeFiberPrecomposition_points (t ≫ q)
      (initialTotalEdgeBase_source q e) (initialTotalEdgeBase_target q e)
      (initialTotalEdgeBase_source q e) (initialRestrictionEdgeBase_eq p q r hr d e).symm
      rfl (hB).symm y
    simp only [pointCoconeMappingIso, eqToIso_refl, Iso.refl_hom, eqToIso.hom] at h
    erw [Category.comp_id] at h
    exact h
  calc
    _ = M ≫ (leftFibrationInitialProjection q b y ≫ K) := by
      rw [initialRestrictionTotalPrecomposition, Category.assoc,
        initialTotalEdgePrecomposition_projection]
    _ = M ≫ ((leftFibrationInitialProjection q b y ≫ C) ≫ K') := by
      rw [hK, Category.assoc (leftFibrationInitialProjection q b y) C K']
    _ = (M ≫ leftFibrationInitialProjection q b y ≫ C) ≫ K' :=
      (Category.assoc _ _ _).symm
    _ = _ := congrArg (· ≫ K') (leftFibrationInitialTotalMap_projection p q r hr d b rfl y)

/-- 通常 Hom 表示では、元の射影の後に既存の同じ Hom 前合成を続けたもの。 -/
lemma initialRestrictionTotalPrecomposition_pinched :
    initialRestrictionTotalPrecomposition p q r hr d e y ≫
        leftFibrationInitialProjection q c y ≫ (leftFibrationInitialBaseIso q c y).hom =
      leftFibrationInitialProjection p d y ≫ (leftFibrationInitialBaseIso p d y).hom ≫
        initialRestrictionHomPrecomposition p q r hr d e y := by
  rw [← Category.assoc (initialRestrictionTotalPrecomposition p q r hr d e y),
    initialRestrictionTotalPrecomposition_projection]
  simp only [initialRestrictionHomPrecomposition, Category.assoc, Iso.hom_inv_id_assoc]

end
end SerrePositivity.InfinityCategories.HomotopyLimits
