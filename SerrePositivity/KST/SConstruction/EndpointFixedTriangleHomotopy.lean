module
public import SerrePositivity.KST.SConstruction.EndpointFixedEdgeSquares
public import SerrePositivity.KST.SConstruction.FamilyCylinderFixedBoundary

/-! # 元の比較三角形から全端点を固定する実円柱
概要：元の三角形の同じ実正方形を比較円柱にし、全区間境界の固定を証明する。
方針：両端の余積表示と tensor の余極限保存で全境界を判定する。
規約：元の全三角形を保持し、端点の固定を点ごとの主張に弱めない。
使われ方：共通辺への二つの元の実三角形を、固定境界空間の外側ホーンへ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
variable {E : SSet.{u}} {x y : E _⦋0⦌}

/-- 同じ両端の元の二辺は、元の区間境界全体上で厳密に一致する。 -/
lemma parallelEdge_boundary_eq (a b : E.Edge x y) :
    (SSet.boundary 1).ι ≫ SSet.yonedaEquiv.symm a.edge =
      (SSet.boundary 1).ι ≫ SSet.yonedaEquiv.symm b.edge := by
  apply HomotopyFunctionComplex.BoundaryOne.isColimit.hom_ext
  rintro ⟨i⟩
  cases i
  · change SSet.boundary.ι (1 : Fin 2) ≫ _ = SSet.boundary.ι (1 : Fin 2) ≫ _
    rw [← Category.assoc, ← Category.assoc, SSet.boundary.ι_ι,
      SSet.Edge.δ_one_yonedaEquiv_symm, SSet.Edge.δ_one_yonedaEquiv_symm]
  · change SSet.boundary.ι (0 : Fin 2) ≫ _ = SSet.boundary.ι (0 : Fin 2) ≫ _
    rw [← Category.assoc, ← Category.assoc, SSet.boundary.ι_ι,
      SSet.Edge.δ_zero_yonedaEquiv_symm, SSet.Edge.δ_zero_yonedaEquiv_symm]

/-- 元の比較三角形の同じ全正方形を、元の二辺の間の実比較円柱にする。 -/
def endpointFixedTriangleHomotopy {a b : E.Edge x y}
    (t : SSet.Edge.CompStruct a (SSet.Edge.id y) b) :
    SSet.Homotopy (SSet.yonedaEquiv.symm a.edge) (SSet.yonedaEquiv.symm b.edge) where
  h := endpointFixedEdgeSquare t
  h₀ := endpointFixedEdgeSquare_zero t
  h₁ := endpointFixedEdgeSquare_one t
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

/-- 元の比較三角形からの円柱は、元の全区間境界を全時刻で厳密に固定する。 -/
lemma endpointFixedTriangleHomotopy_relative {a b : E.Edge x y}
    (t : SSet.Edge.CompStruct a (SSet.Edge.id y) b) :
    ((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫ (endpointFixedTriangleHomotopy t).h =
      fst (SSet.boundary 1).toSSet Δ[1] ≫ (SSet.boundary 1).ι ≫ SSet.yonedaEquiv.symm a.edge := by
  change ((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫ endpointFixedEdgeSquare t = _
  let hc := mapIsColimitOfPreservesOfIsColimit (tensorRight (Δ[1] : SSet.{u}))
    _ _ HomotopyFunctionComplex.BoundaryOne.isColimit
  apply hc.hom_ext
  rintro ⟨i⟩
  cases i
  · change (SSet.boundary.ι (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ _ =
      (SSet.boundary.ι (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ _
    rw [← Category.assoc, ← comp_whiskerRight, SSet.boundary.ι_ι,
      endpointFixedEdgeSquare_source]
    rw [whiskerRight_fst_assoc, ← Category.assoc (SSet.boundary.ι (1 : Fin 2)),
      SSet.boundary.ι_ι, SSet.Edge.δ_one_yonedaEquiv_symm,
      SSet.yonedaEquiv_symm_zero, SSet.comp_const]
  · change (SSet.boundary.ι (0 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ _ =
      (SSet.boundary.ι (0 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ _
    rw [← Category.assoc, ← comp_whiskerRight, SSet.boundary.ι_ι,
      endpointFixedEdgeSquare_target]
    rw [whiskerRight_fst_assoc, ← Category.assoc (SSet.boundary.ι (0 : Fin 2)),
      SSet.boundary.ι_ι, SSet.Edge.δ_zero_yonedaEquiv_symm,
      SSet.yonedaEquiv_symm_zero, SSet.comp_const]

/-- 円柱の元の指定三角形面は、入力した同じ全二単体そのもの。 -/
lemma endpointFixedTriangleHomotopy_triangle {a b : E.Edge x y}
    (t : SSet.Edge.CompStruct a (SSet.Edge.id y) b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower ≫ (endpointFixedTriangleHomotopy t).h =
      SSet.yonedaEquiv.symm t.simplex := endpointFixedEdgeSquare_triangle t

end SerrePositivity.KST.SConstruction
