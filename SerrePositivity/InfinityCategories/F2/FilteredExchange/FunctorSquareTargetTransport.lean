module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorTriangleTargetTransport

/-!
概要：共通対角を持つ元の二面の比較合成を、標的の等式に沿って輸送する。
方針：標的等式を消去し、三円柱と二つの実二単体の外延性を使う。
規約：二面の指定値を保持。使われ方：単位正方形全体の native 表示への接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ対角を共有する二面の指定比較の合成は、標的等式の輸送で変わらない。 -/
lemma functorSquareComparison_app_heq_target
    {B C : SSet.{u + 1}} {F G L J J' : B ⟶ SpaceInfinity.{u}}
    {a : SSet.Homotopy F G} {v : SSet.Homotopy G J} {d : SSet.Homotopy F J}
    {s : SSet.Homotopy F L} {w : SSet.Homotopy L J}
    {v' : SSet.Homotopy G J'} {d' : SSet.Homotopy F J'} {w' : SSet.Homotopy L J'}
    (U : FunctorCompositionTriangle a v d) (D : FunctorCompositionTriangle s w d)
    (U' : FunctorCompositionTriangle a v' d') (D' : FunctorCompositionTriangle s w' d')
    (hj : J = J') (hv : v.h = v'.h) (hd : d.h = d'.h) (hw : w.h = w'.h)
    (hu : U.diagram = U'.diagram) (hl : D.diagram = D'.diagram) (p : C ⟶ B)
    (x : (relativeFunctorSpace (leftUnstraighteningProjection F) p) _⦋0⦌) :
    HEq (((functorTriangleSequentialPostComparison D p).app x).symm ≪≫
      (functorTriangleSequentialPostComparison U p).app x)
      (((functorTriangleSequentialPostComparison D' p).app x).symm ≪≫
        (functorTriangleSequentialPostComparison U' p).app x) := by
  subst J'
  have ev : v = v' := SSet.RelativeMorphism.Homotopy.ext hv
  have ed : d = d' := SSet.RelativeMorphism.Homotopy.ext hd
  have ew : w = w' := SSet.RelativeMorphism.Homotopy.ext hw
  subst v' d' w'
  have eu : U = U' := by cases U; cases U'; cases hu; rfl
  have el : D = D' := by cases D; cases D'; cases hl; rfl
  subst U' D'
  rfl

end SerrePositivity.InfinityCategories.F2
