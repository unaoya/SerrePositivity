module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PointedFiberTransportCoordinates

/-!
概要：coslice fiber の二頂点の表示変更を始点と終点の変更へ分ける。
方針：二つの頂点等式を消去する。
規約：元の等式による移送を保持。使われ方：反転 Kan fiber 比較の正規化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ二頂点の変更は、始点の表示変更と終点 fiber の等式の移送の合成。 -/
lemma cosliceFiberVerticesIso_target_factor {X : SSet.{u}} {x y x' y' : X _⦋0⦌}
    (hx : x = x') (hy : y = y') :
    (cosliceFiberVerticesIso hx hy).hom = (cosliceFiberVerticesIso hx rfl).hom ≫
      eqToHom (congrArg
        (vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x'))) hy) := by
  subst x' y'
  simp [cosliceFiberVerticesIso]

end SerrePositivity.InfinityCategories.F2
