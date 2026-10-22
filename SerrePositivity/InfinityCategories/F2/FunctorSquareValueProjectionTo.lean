module

public import SerrePositivity.InfinityCategories.F2.ConstantTargetValueProjectionTo
public import SerrePositivity.InfinityCategories.F2.FunctorSquareTargetTransport

/-!
概要：元の二面比較を、明示した定値頂点等式に沿って同じ値空間へ射影する。
方針：同じ実円柱・実二面の等式を消去し、元の指定比較を保持する。
規約：合成と逆の指定値を保持。使われ方：五因子の比較を同じホモトピー圏で合成する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の二面比較を固定値へ射影した指定値は、同じ定値標的の表示変更と整合する。 -/
lemma functorSquareComparison_projectionTo_heq
    {B C : SSet.{u + 1}} {F G L : B ⟶ SpaceInfinity.{u}}
    {z z' : SpaceInfinity.{u} _⦋0⦌} {a : SSet.Homotopy F G} {s : SSet.Homotopy F L}
    {v : SSet.Homotopy G (SSet.const z)} {d : SSet.Homotopy F (SSet.const z)}
    {w : SSet.Homotopy L (SSet.const z)} {v' : SSet.Homotopy G (SSet.const z')}
    {d' : SSet.Homotopy F (SSet.const z')} {w' : SSet.Homotopy L (SSet.const z')}
    (U : FunctorCompositionTriangle a v d) (D : FunctorCompositionTriangle s w d)
    (U' : FunctorCompositionTriangle a v' d') (D' : FunctorCompositionTriangle s w' d')
    (hz : z = z') (hv : v.h = v'.h) (hd : d.h = d'.h) (hw : w.h = w'.h)
    (hu : U.diagram = U'.diagram) (hl : D.diagram = D'.diagram) (p : C ⟶ B)
    (x : (relativeFunctorSpace (leftUnstraighteningProjection F) p) _⦋0⦌) :
    HEq (VertexIso.map (((functorTriangleSequentialPostComparison D p).app x).symm ≪≫
      (functorTriangleSequentialPostComparison U p).app x) (constantTargetValueProjectionTo p hz))
      (VertexIso.map (((functorTriangleSequentialPostComparison D' p).app x).symm ≪≫
        (functorTriangleSequentialPostComparison U' p).app x)
        ((constantUnstraighteningRelativeIso p z').hom ≫
          (ihom C).map (pointedSpaceFiberValueEquivalence z').hom)) := by
  subst z'
  have ev : v = v' := SSet.RelativeMorphism.Homotopy.ext hv
  have ed : d = d' := SSet.RelativeMorphism.Homotopy.ext hd
  have ew : w = w' := SSet.RelativeMorphism.Homotopy.ext hw
  subst v' d' w'
  have eu : U = U' := by cases U; cases U'; cases hu; rfl
  have el : D = D' := by cases D; cases D'; cases hl; rfl
  subst U' D'
  rfl

end SerrePositivity.InfinityCategories.F2
