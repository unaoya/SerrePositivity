module

public import SerrePositivity.InfinityCategories.F1.TwistedArrow.HomSpace
public import SerrePositivity.InfinityCategories.F1.Yoneda.YonedaTargetBaseChange
public import SerrePositivity.InfinityCategories.Core.VertexFiberNervePullback

/-!
概要：第二変数を固定した twisted arrow 射影の fiber を、元の両端固定の写像空間と同定する。
方針：底変換の fiber 同型を使い、頂点の定値単体の零次元の等式で端点を正規化する。
規約：元の全空間への包含後の射も厳密に保つ。
使われ方：元の表現可能射影との比較の実際の fiber 写像の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 第二変数固定の包含は、指定頂点を元の両端の対へ写す。 -/
lemma twistedArrowTargetInclusion_vertex {C : SSet.{u}} (x y : C _⦋0⦌) :
    (twistedArrowTargetInclusion y).app (Opposite.op ⦋0⦌) (SSet.opObjEquiv.symm x) =
      (SSet.opObjEquiv.symm x, y) := by
  change (SSet.opObjEquiv.symm x, PinchedHom.constant y 0) = _
  rw [PinchedHom.constant_zero]

/-- 終点固定の実際の射影の fiber は、元の両端固定の twisted arrow 写像空間と同型。 -/
def twistedArrowTargetFiberIso {C : SSet.{u}} (x y : C _⦋0⦌) :
    vertexFiber (twistedArrowTargetProjection y) (SSet.opObjEquiv.symm x) ≅
      twistedArrowHomSpace x y :=
  vertexFiberPullbackIso (twistedArrowProjection C) (twistedArrowTargetInclusion y)
    (SSet.opObjEquiv.symm x) ≪≫
      eqToIso (congrArg (vertexFiber (twistedArrowProjection C))
        (twistedArrowTargetInclusion_vertex x y))

/-- 同型は、元の twisted arrow の全空間への第一射影を保つ。 -/
lemma twistedArrowTargetFiberIso_ι {C : SSet.{u}} (x y : C _⦋0⦌) :
    (twistedArrowTargetFiberIso x y).hom ≫ vertexFiberι (twistedArrowProjection C)
      (SSet.opObjEquiv.symm x, y) =
    vertexFiberι (twistedArrowTargetProjection y) (SSet.opObjEquiv.symm x) ≫
      pullback.fst (twistedArrowProjection C) (twistedArrowTargetInclusion y) := by
  dsimp only [twistedArrowTargetFiberIso, Iso.trans_hom, eqToIso.hom]
  rw [Category.assoc, vertexFiberTransport_ι _ (twistedArrowTargetInclusion_vertex x y),
    vertexFiberPullbackIso_hom_ι]
  rfl

end SerrePositivity.InfinityCategories
