module
public import SerrePositivity.KST.SConstruction.MappingSquareBoundaryData
public import SerrePositivity.KST.SConstruction.KanSpanPastingChoices

/-! # 元の正方形・三角形の辺と端点の表示
概要：実セルから全区間を保って辺を取り出し、指定端点へ移す。
方針：標準辺の tensor と Yoneda の面公式を使う。
規約：端点の表示を変えても raw な一単体を変更しない。
使われ方：三正方形の共有辺と定数外側辺の実比較データへの入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 元の区間を保った、端点の表示だけの変更。 -/
def mappingEdgeRetarget {E : SSet.{u}} {a b a' b' : E _⦋0⦌}
    (e : E.Edge a b) (ha : a = a') (hb : b = b') : E.Edge a' b' :=
  ⟨e.edge, e.src_eq.trans ha, e.tgt_eq.trans hb⟩

/-- 元の正方形の指定した水平辺。 -/
def mappingSquareHorizontalEdge {E : SSet.{u}}
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ E) (b : Fin 2) :
    E.Edge (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex Q 0 b) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex Q 1 b) :=
  SSet.Edge.ofTruncated ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.tensor (SSet.Truncated.Edge.id
    (X := (truncation 2).obj (Δ[1] : SSet.{u})) (stdSimplex.obj₀Equiv.symm b))).map
      ((truncation 2).map Q))

/-- 元の正方形の指定した垂直辺。 -/
def mappingSquareVerticalEdge {E : SSet.{u}}
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ E) (b : Fin 2) :
    E.Edge (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex Q b 0) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex Q b 1) :=
  SSet.Edge.ofTruncated (((SSet.Truncated.Edge.id
    (X := (truncation 2).obj (Δ[1] : SSet.{u})) (stdSimplex.obj₀Equiv.symm b)).tensor
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge).map ((truncation 2).map Q))

/-- 水平辺の Yoneda 表示は、元の全水平区間そのもの。 -/
lemma mappingSquareHorizontalEdge_map {E : SSet.{u}}
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ E) (b : Fin 2) :
    SSet.yonedaEquiv.symm (mappingSquareHorizontalEdge Q b).edge =
      pastingSquareHorizontal b ≫ Q := by
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  exact squareHorizontalEdge_yoneda Q b

/-- 垂直辺の Yoneda 表示も、元の全垂直区間そのもの。 -/
lemma mappingSquareVerticalEdge_map {E : SSet.{u}}
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ E) (b : Fin 2) :
    SSet.yonedaEquiv.symm (mappingSquareVerticalEdge Q b).edge =
      pastingSquareVertical b ≫ Q := by
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  exact squareVerticalEdge_yoneda Q b

/-- 指定した二脚を持つ元の三角形の、残る全適合区間。 -/
def mappingOuterTriangleEdge {E : SSet.{u}} {o a b : E _⦋0⦌}
    (l : E.Edge o a) (r : E.Edge o b) (t : E _⦋2⦌)
    (h₂ : E.δ 2 t = l.edge) (h₁ : E.δ 1 t = r.edge) : E.Edge a b := by
  refine ⟨E.δ 0 t, ?_, ?_⟩
  · exact ((E.δ_comp_δ_apply (i := (0 : Fin 2)) (j := 1) (by decide) t).symm).trans
      ((congrArg (E.δ 0) h₂).trans l.tgt_eq)
  · exact ((E.δ_comp_δ_apply (i := (0 : Fin 2)) (j := 0) (by decide) t).symm).trans
      ((congrArg (E.δ 0) h₁).trans r.tgt_eq)

/-- 元の三角形全体と三辺を厳密に保持する。 -/
def mappingOuterTriangle {E : SSet.{u}} {o a b : E _⦋0⦌}
    (l : E.Edge o a) (r : E.Edge o b) (t : E _⦋2⦌)
    (h₂ : E.δ 2 t = l.edge) (h₁ : E.δ 1 t = r.edge) :
    SSet.Edge.CompStruct l (mappingOuterTriangleEdge l r t h₂ h₁) r :=
  ⟨t, h₂, rfl, h₁⟩

end SerrePositivity.KST.SConstruction
