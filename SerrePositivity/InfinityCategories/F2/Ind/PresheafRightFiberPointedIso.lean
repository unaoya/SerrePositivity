module

public import SerrePositivity.InfinityCategories.F2.Ind.PresheafDensityEvaluation
public import SerrePositivity.InfinityCategories.Stable.VertexFiberOpposite
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallLeftUnstraighteningOverMap
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningFiberTransport
public import SerrePositivity.InfinityCategories.F1B.KanVertexFiberSquareIso

/-!
概要：元の right unstraightening の反転 fiber を、同じ前層の評価の pointed fiber と比較する。
方針：反転・全空間の縮小・引き戻しの標準 fiber 同型を続ける。
規約：元の fiber と指定された同じ評価頂点への包含を保持する。
使われ方：元の始点固定評価の弱同値を密度の実際の値写像へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) (x : C _⦋0⦌)
local notation "p" => smallRightUnstraighteningProjection F
local notation "z" => presheafDensityEvaluationVertex F x

/-- 元の反転した right fiber は、元の小さい left fiber と厳密に同型。 -/
def presheafRightFiberLeftIso : (vertexFiber p x).op ≅
    vertexFiber (smallLeftUnstraighteningProjection F) (SSet.opObjEquiv.symm x) :=
  vertexFiberOpIso p x ≪≫ vertexFiberTotalIso (SSet.opFunctor.map p)
    (smallLeftUnstraighteningProjection F) (smallRightUnstraighteningOppositeIso F)
    (smallRightUnstraighteningProjection_op F).symm (SSet.opObjEquiv.symm x)

/-- 同じ小さい fiber 比較は、元の反転全空間への包含を保つ。 -/
lemma presheafRightFiberLeftIso_ι :
    (presheafRightFiberLeftIso F x).hom ≫
      vertexFiberι (smallLeftUnstraighteningProjection F) (SSet.opObjEquiv.symm x) =
    SSet.opFunctor.map (vertexFiberι p x) ≫ (smallRightUnstraighteningOppositeIso F).hom := by
  rw [presheafRightFiberLeftIso, Iso.trans_hom, Category.assoc]
  change (vertexFiberOpIso p x).hom ≫
    vertexFiberMap _ _ _ (smallRightUnstraighteningProjection_op F).symm _ ≫ _ = _
  rw [vertexFiberMap_ι, ← Category.assoc]
  rfl

/-- 元の反転 fiber の持ち上げは、同じ指定評価頂点の pointed fiber と厳密に同型。 -/
def presheafRightFiberPointedIso :
    (SSet.uliftFunctor.{u + 1, u}).obj (vertexFiber p x).op ≅
      vertexFiber pointedSpaceProjection z :=
  (SSet.uliftFunctor.{u + 1, u}).mapIso (presheafRightFiberLeftIso F x) ≪≫
    smallLeftUnstraighteningFiberIso F (SSet.opObjEquiv.symm x) ≪≫
      leftUnstraighteningFiberIso F (ULift.up (SSet.opObjEquiv.symm x)) ≪≫
        eqToIso (congrArg (vertexFiber pointedSpaceProjection)
          (presheafDensityEvaluationVertex_value F x).symm)

/-- 同じ pointed fiber 比較の全体への包含は、元の全空間比較を続けた射そのもの。 -/
lemma presheafRightFiberPointedIso_ι :
    (presheafRightFiberPointedIso F x).hom ≫ vertexFiberι pointedSpaceProjection z =
    (SSet.uliftFunctor.{u + 1, u}).map
      (SSet.opFunctor.map (vertexFiberι p x) ≫ (smallRightUnstraighteningOppositeIso F).hom) ≫
        (smallLeftUnstraighteningIso F).hom ≫ pullback.fst pointedSpaceProjection F := by
  simp only [presheafRightFiberPointedIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [F1B.kanVertexFiberι_eqTransport pointedSpaceProjection
    (presheafDensityEvaluationVertex_value F x).symm, leftUnstraighteningFiberIso_hom_ι]
  have hs := congrArg (fun f =>
    (SSet.uliftFunctor.{u + 1, u}).map (presheafRightFiberLeftIso F x).hom ≫ f ≫
      pullback.fst pointedSpaceProjection F)
    (smallLeftUnstraighteningFiberIso_hom_ι F (SSet.opObjEquiv.symm x))
  simpa only [← Category.assoc, ← Functor.map_comp, presheafRightFiberLeftIso_ι] using hs

end SerrePositivity.InfinityCategories.F2.Ind
