module

public import SerrePositivity.EInfinity.FrameHom.FrameRoofTarget
public import SerrePositivity.InfinityCategories.F1B.KanScaffoldPullbackFiber
public import SerrePositivity.InfinityCategories.Derived.RoofTargetFunctor

/-!
# 元の実屋根の指定次数 fiber と同じ pinched Hom

概要：元の次数の fiber を、元の qA(n) と qY を結ぶ実写像空間と厳密に同定する。
方針：引き戻しの fiber 同型と、元の頂点・点図式の全写像の等式だけを使う。
規約：指定次数・元の q・元の全錐の単体を保ち、別の頂点を選ばない。
使われ方：屋根 corner の全体評価を既存の Kan Hom 比較へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.FrameHom.FrameArrows
open CategoryTheory Limits Opposite SSet SerrePositivity.InfinityCategories
open scoped Simplicial
variable {I C : Type u} [Category.{u} I] [Category.{u} C] (A : I ⥤ C) (Y : C)
  {E : SSet.{u}} (q : nerve C ⟶ E)

lemma roofTargetFrameVertex (n : I) :
    (nerveMap A ≫ q).app (op ⦋0⦌) (nerveVertex n) = q.app (op ⦋0⦌) (nerveVertex (A.obj n)) := by
  rw [NatTrans.comp_app_apply]
  exact congrArg (q.app (op ⦋0⦌)) (nerveMap_app_mk₀ A n)

def roofTargetFiberPinchedIso (n : I) :
    vertexFiber (roofTargetProjection A Y q) (nerveVertex n) ≅
      pinchedHom (q.app (op ⦋0⦌) (nerveVertex (A.obj n)))
        (q.app (op ⦋0⦌) (nerveVertex Y)) :=
  KanSection.vertexFiberPullbackIso
    (sliceOverProjection (SSet.yonedaEquiv.symm (nerveVertex Y) ≫ q))
    (nerveMap A ≫ q) (nerveVertex n) ≪≫
  eqToIso (congrArg (vertexFiber (sliceOverProjection
    (SSet.yonedaEquiv.symm (nerveVertex Y) ≫ q))) (roofTargetFrameVertex A q n)) ≪≫
  eqToIso (congrArg (fun p => vertexFiber (sliceOverProjection p)
    (q.app (op ⦋0⦌) (nerveVertex (A.obj n)))) (roofTargetPoint q (nerveVertex Y))) ≪≫
  (pinchedHomSliceFiberIso (q.app (op ⦋0⦌) (nerveVertex (A.obj n)))
    (q.app (op ⦋0⦌) (nerveVertex Y))).symm

end SerrePositivity.EInfinity.FrameHom.FrameArrows
