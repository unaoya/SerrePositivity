module
public import SerrePositivity.KST.Spectra.ThreeEdgeTransportSquare
public import SerrePositivity.KST.SConstruction.MappingSquareCornerIdentities

/-! # 元の比較三角形を保つ端点固定の実正方形
概要：元の二辺と恒等終辺の実三角形を、両端を全時刻で固定する正方形にする。
方針：元の三角形と同じ対角辺の退化三角形を貼り合わせる。
規約：元の全二単体と二辺全体を保持し、端点の固定も実射の等号で記録する。
使われ方：有限補正列の合成を比較する実二次元円柱。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open Spectra
open scoped Simplicial
variable {E : SSet.{u}} {x y : E _⦋0⦌} {a b : E.Edge x y}
  (t : SSet.Edge.CompStruct a (SSet.Edge.id y) b)

/-- 元の二辺を結ぶ、両端が同じ恒等辺の実輸送データ。 -/
def endpointFixedEdgeTransport : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport a (SSet.Edge.id x) b :=
  ⟨b, SSet.Edge.id y, SSet.Edge.CompStruct.idComp b, t⟩

/-- 元の比較三角形を全体として保持する、端点固定の実正方形。 -/
def endpointFixedEdgeSquare : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ E :=
  ThreeEdgeTransport.square (endpointFixedEdgeTransport t)

/-- 零面は元の第一辺の全区間そのもの。 -/
lemma endpointFixedEdgeSquare_zero :
    SSet.ι₀ ≫ endpointFixedEdgeSquare t = SSet.yonedaEquiv.symm a.edge :=
  ThreeEdgeTransport.square_zero _

/-- 一面も元の第二辺の全区間そのもの。 -/
lemma endpointFixedEdgeSquare_one :
    SSet.ι₁ ≫ endpointFixedEdgeSquare t = SSet.yonedaEquiv.symm b.edge :=
  ThreeEdgeTransport.square_one _

/-- 元の始点は全時刻で厳密に固定する。 -/
lemma endpointFixedEdgeSquare_source :
    (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ endpointFixedEdgeSquare t =
      SSet.const x := by
  rw [endpointFixedEdgeSquare, ThreeEdgeTransport.square_start]
  change snd (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫
    SSet.yonedaEquiv.symm (SSet.Edge.id x).edge = SSet.const x
  rw [mappingIdentityEdge_map, SSet.comp_const]

/-- 元の終点も全時刻で厳密に固定する。 -/
lemma endpointFixedEdgeSquare_target :
    (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ endpointFixedEdgeSquare t =
      SSet.const y := by
  rw [endpointFixedEdgeSquare, ThreeEdgeTransport.square_finish]
  change snd (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫
    SSet.yonedaEquiv.symm (SSet.Edge.id y).edge = SSet.const y
  rw [mappingIdentityEdge_map, SSet.comp_const]

/-- 下側の全二単体は、入力した同じ元の比較三角形。 -/
lemma endpointFixedEdgeSquare_triangle :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower ≫ endpointFixedEdgeSquare t = SSet.yonedaEquiv.symm t.simplex :=
  ThreeEdgeTransport.square_lower _

/-- 始点側の指定 zero 垂直区間も、元の対応する端点の全時刻の定数族。 -/
lemma endpointFixedEdgeSquare_vertical_zero :
    pastingSquareVertical 0 ≫ endpointFixedEdgeSquare t = SSet.const x := by
  have hp : pastingSquareVertical.{u} 0 =
      lift (stdSimplex.isTerminalObj₀.from (Δ[1] : SSet.{u})) (𝟙 _) ≫
        (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) := by
    rw [stdSimplex.δ_one_eq_const]
    rfl
  rw [hp, Category.assoc, endpointFixedEdgeSquare_source, SSet.comp_const]

/-- 終点側の指定 one 垂直区間も、元の対応する端点の全時刻の定数族。 -/
lemma endpointFixedEdgeSquare_vertical_one :
    pastingSquareVertical 1 ≫ endpointFixedEdgeSquare t = SSet.const y := by
  have hp : pastingSquareVertical.{u} 1 =
      lift (stdSimplex.isTerminalObj₀.from (Δ[1] : SSet.{u})) (𝟙 _) ≫
        (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u})) := by
    rw [stdSimplex.δ_zero_eq_const]
    rfl
  rw [hp, Category.assoc, endpointFixedEdgeSquare_target, SSet.comp_const]

end SerrePositivity.KST.SConstruction
