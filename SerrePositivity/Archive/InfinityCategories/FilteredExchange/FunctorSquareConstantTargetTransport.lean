module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorSquareTargetTransport
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ConstantUnstraighteningRelativeProjection

/-!
概要：元の二面比較の値への像を、定値標的の頂点の等式に沿って輸送する。
方針：標的等式を消去し、同じ三円柱・二面の外延性を使う。
規約：指定値と全係数を保持。使われ方：元の余錐頂点と native 頂点の値の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ定値頂点の表示変更は、元の二面比較の元の値への像を保持する。 -/
lemma functorSquareComparison_value_heq_target
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
      (functorTriangleSequentialPostComparison U p).app x)
      ((constantUnstraighteningRelativeIso p z).hom ≫
        (ihom C).map (pointedSpaceFiberValueEquivalence z).hom))
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
