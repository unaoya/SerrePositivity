module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CommaUnitTransportComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.IntervalPrecompositionTriangle

/-!
概要：comma fiber の任意の点が表す辺から、局所的な区間比較を構成する。
方針：回収した辺の Hom 類で前合成し、同じ辺を持つ合成三角形を選ぶ。
規約：関手 F や大域単位を入力にせず、G と二重 fiber の点だけを使う。
使われ方：局所比較を comma の普遍輸送と照合するための三辺を供給する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {X Y : SSet.{u}} [Quasicategory X]
variable {G : Y ⟶ X} {x : X _⦋0⦌} {y₀ : Y _⦋0⦌}

/-- 概要：指定 comma 点の辺による区間比較。
方針：G の作用の後で回収した辺の類により前合成する。
規約：F と大域単位は要求しない。
使われ方：局所的な写像空間条件と輸送の比較。 -/
def unitIntervalMapAt
    (v : (vertexFiber (F1B.unitCommaFiberProjection G x) y₀) _⦋0⦌) (y : Y _⦋0⦌) :
    intervalMappingSpace y₀ y ⟶ intervalMappingSpace x (G.app (Opposite.op ⦋0⦌) y) :=
  intervalFunctorMap G y₀ y ≫ intervalPrecompose (G.app (Opposite.op ⦋0⦌) y)
    (Truncated.HomotopyCategory.homMk (commaTargetFiberArrow G x y₀ v).toTruncated)

/-- 概要：大域単位の comma 点で局所比較は既存の比較に一致する。
方針：同じ辺の Hom 類が指定単位成分であることを使う。
規約：既存の比較写像の選択を保持する厳密な等式。
使われ方：大域版を局所版の特殊化として利用する。 -/
lemma unitIntervalMapAt_unitCommaSectionTargetFiberVertex [Quasicategory Y] {F : X ⟶ Y}
    (η : FunctorHom (𝟙 X) (F ≫ G)) (a : X _⦋0⦌) (y : Y _⦋0⦌) :
    unitIntervalMapAt (unitCommaSectionTargetFiberVertex η a) y = unitIntervalMap η a y := by
  rw [unitIntervalMapAt, unitCommaSectionTargetFiberArrow_hom]
  rfl

omit [Quasicategory X] in
/-- 概要：二重 fiber の点の定値区間族は元の comma の定値族を表す。
方針：区間模型の展開と二重包含の自然性を使う。
規約：ホモトピーの射の厳密な一致を述べる。
使われ方：輸送円柱の始端を元の点に固定する。 -/
lemma commaTargetFiber_constant_homotopy {A : SSet.{u}}
    (v : (vertexFiber (F1B.unitCommaFiberProjection G x) y₀) _⦋0⦌) :
    (intervalFamilyHomotopy (SSet.const (X := A)
      (intervalMappingVertexOfEdge (commaTargetFiberArrow G x y₀ v)))).h =
      (unitCommaFiberHomotopy (SSet.const (X := A) v.val)).h := by
  have hv : intervalMappingVertexOfEdge (commaTargetFiberArrow G x y₀ v) =
      (F1B.unitCommaFiberToInterval G x y₀).app _ v :=
    (intervalMappingEdgeVertexEquiv _ _).apply_symm_apply _
  rw [hv]
  change (β_ A (Δ[1] : SSet.{u})).hom ≫ intervalMappingUncurry
    (SSet.const ((F1B.unitCommaFiberToInterval G x y₀).app _ v)) =
      (β_ A (Δ[1] : SSet.{u})).hom ≫ unitCommaUncurry
        (SSet.const v.val ≫ vertexFiberι (unitCommaSource G) x)
  rw [← SSet.const_comp v (F1B.unitCommaFiberToInterval G x y₀)]
  rw [intervalMappingUncurry_precomp, F1B.unitCommaFiberToInterval_uncurry,
    ← unitCommaUncurry_precomp]
  simp only [← Category.assoc, SSet.const_comp]
  rfl

/-- 概要：局所比較の指定三辺を持つ普遍合成三角形。
方針：前合成の族の公式から三辺固定の三角形を回収する。
規約：元の点の辺と選択済みの局所比較を保つ。
使われ方：comma 内の局所輸送円柱を作る。 -/
def unitIntervalCompositionTriangleAt
    (v : (vertexFiber (F1B.unitCommaFiberProjection G x) y₀) _⦋0⦌) (y : Y _⦋0⦌) :
    FunctorCompositionTriangle
      (intervalFamilyHomotopy (SSet.const (X := intervalMappingSpace y₀ y)
        (intervalMappingVertexOfEdge (commaTargetFiberArrow G x y₀ v))))
      (intervalFamilyHomotopy (intervalFunctorMap G y₀ y))
      (intervalFamilyHomotopy (unitIntervalMapAt v y)) := by
  apply Classical.choice
  apply nonempty_functorCompositionTriangle_of_homEq
  change intervalFamilyHom _ ≫ intervalFamilyHom _ = intervalFamilyHom _
  rw [intervalFamilyHom_const_edge, unitIntervalMapAt, intervalPrecompose_family]

end SerrePositivity.InfinityCategories.HomotopyLimits
