module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.NativePointedTriangleFaceSections
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.NativePointedConeSections

/-!
概要：native 三角形の図式側の面の切断族を、元の錐の切断族の辺制限と厳密に同定する。
方針：零番目の面の底の表示を元の図式へ移し、相対 uncurry の単射性で全族を比較する。
規約：元の辺と全 pointed 錐を保持。使われ方：二辺の切断の引き戻しへの指定比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {K A : SSet.{u + 1}} {d : K ⟶ SpaceInfinity.{u}} (c : JoinCone d)
  (s : A ⟶ PointedSpaceInfinity.{u}) (hs : s ≫ pointedSpaceProjection = SSet.const c.vertex)
  (k : K _⦋1⦌)
local notation "e" => SSet.yonedaEquiv.symm k
local notation "D" => SSet.yonedaEquiv.symm (nativeConeTriangle c k)
local notation "N" => nativePointedConeTriangleLift c s hs k
local notation "hN" => nativePointedConeTriangleLift_projection c s hs k

/-- 三角形の図式側の辺の底は、元の図式の同じ辺そのもの。 -/
lemma nativeConeTriangle_diagram_edge : stdSimplex.δ (0 : Fin 3) ≫ D = e ≫ d := by
  rw [nativeConeTriangle, Equiv.symm_apply_apply, ← Category.assoc,
    coneTriangleInclusion_zero, Category.assoc, c.property]

/-- 三角形の面の図式表示を、元の形状の辺上の切断空間へ揃える。 -/
def nativePointedTriangleDiagramSections : A ⟶
    relativeFunctorSpace pointedSpaceProjection (e ≫ d) :=
  pointedTriangleFaceSections D N hN 0 ≫
    eqToHom (congrArg (relativeFunctorSpace pointedSpaceProjection)
      (nativeConeTriangle_diagram_edge c k))

/-- 正規化した三角形の図式側の切断族は、元の全錐の切断族の同じ辺への制限に等しい。 -/
lemma nativePointedTriangleDiagramSections_eq :
    nativePointedTriangleDiagramSections c s hs k =
      nativePointedConeSections c s hs ≫ relativeFunctorPre pointedSpaceProjection d e := by
  apply relativeFunctorUncurry_injective pointedSpaceProjection (e ≫ d)
  rw [nativePointedTriangleDiagramSections,
    HomotopyLimits.relativeFunctorUncurry_eqToHom pointedSpaceProjection
      (nativeConeTriangle_diagram_edge c k), pointedTriangleFaceSections_uncurry]
  have he := relativeFunctorUncurry_pre (p := pointedSpaceProjection)
    (nativePointedConeSections c s hs) e
  rw [nativePointedConeSections_uncurry] at he
  rw [he, nativePointedConeTriangleLift, ← Category.assoc, ← comp_whiskerRight,
    coneTriangleInclusion_zero, comp_whiskerRight, Category.assoc]

end SerrePositivity.InfinityCategories.F2
