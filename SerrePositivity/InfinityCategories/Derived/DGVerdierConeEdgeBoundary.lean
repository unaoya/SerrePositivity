module
public import SerrePositivity.InfinityCategories.Derived.DGVerdierOver
public import SerrePositivity.InfinityCategories.Derived.RoofSliceTetrahedronInverse
public import SerrePositivity.InfinityCategories.Derived.FullSubcomplexTriangleLift

/-! # 指定実図式辺と二脚の一次整合性の具体的境界

概要：実分母図式の指定辺と共通始点からの二脚を、元の dg nerve の三次外ホーンへ移す。
方針：三つの回収三角形を貼り、指定ホーンの充填から実分母内の合成二単体を回収する。
規約：実図式辺と二脚を厳密に保持。ホーン充填の存在は別に証明する。
使われ方：有限 ∞ 図式の共通始錐の一次整合性を解く入口。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (P : Set D) (x : D)
variable {d s t : (dgVerdierOver A D P x : SSet.{max u v}) _⦋0⦌}
variable (u : Truncated.Edge (X := (truncation 2).obj (dgVerdierOver A D P x : SSet)) d s)
variable (e : Truncated.Edge (X := (truncation 2).obj (dgVerdierOver A D P x : SSet)) s t)
variable (w : Truncated.Edge (X := (truncation 2).obj (dgVerdierOver A D P x : SSet)) d t)

/-- 指定図式辺と二脚を、元の dg nerve の最後外ホーンとして表示する。 -/
def dgVerdierConeEdgeHorn : (Λ[3, 3] : SSet.{max u v}) ⟶ dgNerve A D :=
  roofPointSliceOuterHorn
    ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex x))
    (u.map ((truncation 2).map (dgVerdierOver A D P x).ι))
    (e.map ((truncation 2).map (dgVerdierOver A D P x).ι))
    (w.map ((truncation 2).map (dgVerdierOver A D P x).ι))

/-- ホーンの零面は元の指定実図式辺。 -/
lemma dgVerdierConeEdgeHorn_face0 :
    horn.ι (3 : Fin 4) 0 (by decide) ≫ dgVerdierConeEdgeHorn A D P x u e w =
      roofPointSliceTriangle ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex x))
        ((dgVerdierOver A D P x).ι.app (Opposite.op ⦋1⦌) e.edge) :=
  roofPointSliceOuterHorn_face0 _ _ _ _

/-- ホーンの一面は第二脚。 -/
lemma dgVerdierConeEdgeHorn_face1 :
    horn.ι (3 : Fin 4) 1 (by decide) ≫ dgVerdierConeEdgeHorn A D P x u e w =
      roofPointSliceTriangle ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex x))
        ((dgVerdierOver A D P x).ι.app (Opposite.op ⦋1⦌) w.edge) :=
  roofPointSliceOuterHorn_face1 _ _ _ _

/-- ホーンの二面は第一脚。 -/
lemma dgVerdierConeEdgeHorn_face2 :
    horn.ι (3 : Fin 4) 2 (by decide) ≫ dgVerdierConeEdgeHorn A D P x u e w =
      roofPointSliceTriangle ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex x))
        ((dgVerdierOver A D P x).ι.app (Opposite.op ⦋1⦌) u.edge) :=
  roofPointSliceOuterHorn_face2 _ _ _ _

/-- 元の dg nerve の指定三次ホーンの充填を、実分母内の指定三辺の整合性へ戻す。 -/
def dgVerdierConeEdgeCompStructOfFiller (F : Δ[3] ⟶ dgNerve A D)
    (hF : (horn 3 3).ι ≫ F = dgVerdierConeEdgeHorn A D P x u e w) :
    Truncated.Edge.CompStruct u e w := by
  let a := (SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex x)
  let U := u.map ((truncation 2).map (dgVerdierOver A D P x).ι)
  let E := e.map ((truncation 2).map (dgVerdierOver A D P x).ι)
  let W := w.map ((truncation 2).map (dgVerdierOver A D P x).ι)
  have h₀ : SSet.stdSimplex.δ (0 : Fin 4) ≫ F = roofPointSliceTriangle a E.edge := by
    rw [← horn.ι_ι_assoc (3 : Fin 4) 0 (by decide), hF]
    exact dgVerdierConeEdgeHorn_face0 A D P x u e w
  have h₁ : SSet.stdSimplex.δ (1 : Fin 4) ≫ F = roofPointSliceTriangle a W.edge := by
    rw [← horn.ι_ι_assoc (3 : Fin 4) 1 (by decide), hF]
    exact dgVerdierConeEdgeHorn_face1 A D P x u e w
  have h₂ : SSet.stdSimplex.δ (2 : Fin 4) ≫ F = roofPointSliceTriangle a U.edge := by
    rw [← horn.ι_ι_assoc (3 : Fin 4) 2 (by decide), hF]
    exact dgVerdierConeEdgeHorn_face2 A D P x u e w
  exact fullSubcomplexTriangleLift (IsDGVerdierOverVertex A D P x) u e w
    (roofPointSliceCompStructOfTetrahedron a U E W F h₀ h₁ h₂)

end SerrePositivity.InfinityCategories
