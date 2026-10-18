module

public import SerrePositivity.InfinityCategories.Core.FunctorHomotopy

/-!
概要：関手単体集合の固定した頂点での評価。
方針：内部 Hom の各次数の関手を、頂点の定値単体に適用する。
規約：評価は単体集合の射として構成する。
使われ方：Kerodon §4.5.1、§4.8.4 の可逆な自然変換の成分。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：関手単体集合を始域の一頂点で評価する射。
方針：次数 d の関手単体に恒等写像と頂点の定値 d 単体を代入する。
規約：始域と標的に quasicategory 性は不要。
使われ方：Kerodon §4.5.1 の関手の辺の成分。 -/
def evaluateFunctorAt {X Y : SSet.{u}} (x : X _⦋0⦌) : (ihom X).obj Y ⟶ Y where
  app d := ↾fun F ↦ F.app d (𝟙 d) (PinchedHom.constant x d.unop.len)
  naturality {d e} α := by
    apply ConcreteCategory.hom_ext
    intro F
    have h := ConcreteCategory.congr_hom (F.naturality α (𝟙 d))
      (PinchedHom.constant x d.unop.len)
    change F.app e ((𝟙 d) ≫ α) (X.map α (PinchedHom.constant x d.unop.len)) =
      Y.map α (F.app d (𝟙 d) (PinchedHom.constant x d.unop.len)) at h
    have hc : X.map α (PinchedHom.constant x d.unop.len) =
        PinchedHom.constant x e.unop.len := PinchedHom.constant_pullback x α.unop
    change F.app e (α ≫ 𝟙 e) (PinchedHom.constant x e.unop.len) =
      Y.map α (F.app d (𝟙 d) (PinchedHom.constant x d.unop.len))
    simpa only [Category.id_comp, Category.comp_id, hc] using h

/-- 概要：関手の頂点表示を評価すると元の射による頂点の像。
方針：零次元の定値単体を計算する。
規約：x は始域の固定した頂点。
使われ方：Kerodon §4.5.1 の頂点での評価。 -/
lemma evaluateFunctorAt_functorVertex {X Y : SSet.{u}} (x : X _⦋0⦌) (f : X ⟶ Y) :
    (evaluateFunctorAt (Y := Y) x).app (Opposite.op ⦋0⦌) (functorVertex f) =
      f.app (Opposite.op ⦋0⦌) x := by
  change f.app (Opposite.op ⦋0⦌) (PinchedHom.constant x 0) = _
  rw [pinchedConstant_zero]

/-- 概要：関手の辺の uncurry の頂点での辺は、評価による辺の像。
方針：恒等辺が頂点の定値一単体であることを使う。
規約：先頭と終端の固定条件は辺の等式に影響しない。
使われ方：Kerodon §4.8.4 の可逆な成分を持つホモトピー。 -/
lemma evaluateFunctorAt_edge {X Y : SSet.{u}} {f g : X ⟶ Y}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom X).obj Y))
      (functorVertex f) (functorVertex g)) (x : X _⦋0⦌) :
    (simplicialHomotopyVertexEdge (simplicialHomotopyOfFunctorEdge e) x).edge =
      (evaluateFunctorAt (Y := Y) x).app (Opposite.op ⦋1⦌) e.edge := by
  change e.edge.app (Opposite.op ⦋1⦌) (stdSimplex.objEquiv homotopyIntervalEdge.edge).op
    (SSet.Truncated.Edge.id (X := (truncation 2).obj X) x).edge =
      e.edge.app (Opposite.op ⦋1⦌) (𝟙 (Opposite.op ⦋1⦌)) (PinchedHom.constant x 1)
  have h : stdSimplex.objEquiv (homotopyIntervalEdge.{u}).edge = 𝟙 ⦋1⦌ := by
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro i
    fin_cases i <;> rfl
  rw [h, pinchedConstant_one]
  rfl

/-- 概要：可逆な関手の辺から得るホモトピーの各頂点での辺は可逆。
方針：評価の射で可逆な辺を写し、前の計算で同じ辺であることを確認する。
規約：標的 Y を quasicategory とする。
使われ方：Kerodon §4.8.4 の同値による境界充填の移送。 -/
lemma simplicialHomotopyOfFunctorEdge_vertex_isInvertible {X Y : SSet.{u}}
    [Quasicategory Y] {f g : X ⟶ Y}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom X).obj Y))
      (functorVertex f) (functorVertex g)) (he : IsInvertibleEdge e) (x : X _⦋0⦌) :
    IsInvertibleEdge
      (simplicialHomotopyVertexEdge (simplicialHomotopyOfFunctorEdge e) x).toTruncated := by
  have hm := he.map (evaluateFunctorAt (Y := Y) x)
  exact (isInvertibleEdge_congr (evaluateFunctorAt_edge e x)).mpr hm

end SerrePositivity.InfinityCategories
