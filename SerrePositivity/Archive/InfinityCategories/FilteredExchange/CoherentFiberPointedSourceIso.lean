module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanPointedConeLift
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraighteningFiberTransport

/-!
概要：元の小さい fiber の pointed 始点族を、同じ値の pointed fiber への厳密な同型に表示する。
方針：縮小の fiber 同型と普遍射影の引き戻しの fiber 同型を合成する。
規約：頂点は元の図式の値そのもの。使われ方：端点評価を元の小さい fiber へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌)

/-- 元の始点族を表す同型。底の頂点は元の図式の値を使う。 -/
def coherentFiberPointedSourceIso :
    coherentNativeTriangleFiberParameters F b ≅
      vertexFiber pointedSpaceProjection (F.app (Opposite.op ⦋0⦌) (ULift.up b)) :=
  smallLeftUnstraighteningFiberIso F b ≪≫ leftUnstraighteningFiberIso F (ULift.up b)

/-- この同型の順方向は元の pointed 始点族を厳密に保持する。 -/
lemma coherentFiberPointedSourceIso_hom_ι :
    (coherentFiberPointedSourceIso F b).hom ≫
      vertexFiberι pointedSpaceProjection (F.app (Opposite.op ⦋0⦌) (ULift.up b)) =
        coherentCospanFiberPointedSource F b := by
  rw [coherentFiberPointedSourceIso, Iso.trans_hom, Category.assoc,
    leftUnstraighteningFiberIso_hom_ι, ← Category.assoc,
    smallLeftUnstraighteningFiberIso_hom_ι]
  rfl

end SerrePositivity.InfinityCategories.F2
