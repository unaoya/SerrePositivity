module

public import SerrePositivity.InfinityCategories.F1B.Adjunction.UnitCommaFamilies
public import SerrePositivity.InfinityCategories.Core.CocartesianPathSpace

/-!
概要：comma の矢印射影の二つの端点を始域・標的の射影で回収する。
方針：区間図式の uncurry の端点公式を評価射で表す。
規約：単位の選択や quasicategory 性は不要。
使われ方：B1 の標的を固定した cartesian lift の端点の認識。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：comma の矢印の始点評価は始域射影。
方針：展開した矢印の零端点公式を使う。
規約：射として厳密に一致する。
使われ方：cartesian lift の始域の照合。 -/
lemma unitCommaArrow_evaluate_zero {X Y : SSet.{u}} (G : Y ⟶ X) :
    unitCommaArrow G ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      unitCommaSource G := by
  have h := unitCommaUncurry_zero (𝟙 (unitComma G))
  have he : unitCommaArrow G ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      prismEndpoint 0 (unitComma G) ≫ uncurry (unitCommaArrow G) := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro v
    rfl
  rw [he]
  simpa only [unitCommaUncurry, Category.id_comp] using h

/-- 概要：comma の矢印の終点評価は標的射影の後の G。
方針：展開した矢印の一端点公式を使う。
規約：射として厳密に一致する。
使われ方：標的を固定した lift の矢印の端点の照合。 -/
lemma unitCommaArrow_evaluate_one {X Y : SSet.{u}} (G : Y ⟶ X) :
    unitCommaArrow G ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      unitCommaTarget G ≫ G := by
  have h := unitCommaUncurry_one (𝟙 (unitComma G))
  have he : unitCommaArrow G ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      prismEndpoint 1 (unitComma G) ≫ uncurry (unitCommaArrow G) := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro v
    rfl
  rw [he]
  simpa only [unitCommaUncurry, Category.id_comp] using h

/-- 概要：comma の頂点の矢印を X の実際の区間図式にする。
方針：矢印射影の頂点に内部 Hom の零単体表示同値を適用する。
規約：ホモトピー類から新しい代表を選ばない。
使われ方：cartesian lift の合成三角形に渡す指定辺。 -/
noncomputable def unitCommaVertexArrow {X Y : SSet.{u}} (G : Y ⟶ X)
    (v : (unitComma G) _⦋0⦌) : (Δ[1] : SSet.{u}) ⟶ X :=
  (functorVertexEquiv Δ[1] X).symm ((unitCommaArrow G).app (Opposite.op ⦋0⦌) v)

/-- 概要：頂点の矢印表示を戻すと元の矢印射影の頂点に一致する。
方針：内部 Hom の表示同値の両逆。
規約：厳密な一致。
使われ方：lift の終点を元の comma 頂点に戻す。 -/
lemma unitCommaVertexArrow_functorVertex {X Y : SSet.{u}} (G : Y ⟶ X)
    (v : (unitComma G) _⦋0⦌) :
    functorVertex (unitCommaVertexArrow G v) = (unitCommaArrow G).app (Opposite.op ⦋0⦌) v :=
  (functorVertexEquiv Δ[1] X).apply_symm_apply _

/-- 概要：comma の頂点は始域射影から G を続けた標的射影への指定辺を与える。
方針：区間頂点の辺の両端を、矢印射影の二つの評価公式で揃える。
規約：元の矢印の一単体を保持する。
使われ方：始域の辺との合成による cartesian lift の構成。 -/
noncomputable def unitCommaVertexEdge {X Y : SSet.{u}} (G : Y ⟶ X)
    (v : (unitComma G) _⦋0⦌) :
    SSet.Truncated.Edge (X := (truncation 2).obj X)
      ((unitCommaSource G).app (Opposite.op ⦋0⦌) v)
      (G.app (Opposite.op ⦋0⦌) ((unitCommaTarget G).app (Opposite.op ⦋0⦌) v)) where
  edge := intervalFunctorVertexEdge ((unitCommaArrow G).app (Opposite.op ⦋0⦌) v)
  src_eq := by
    have h := (intervalFunctorVertexTypedEdge
      ((unitCommaArrow G).app (Opposite.op ⦋0⦌) v)).src_eq
    exact h.trans (ConcreteCategory.congr_hom
      (NatTrans.congr_app (unitCommaArrow_evaluate_zero G) (Opposite.op ⦋0⦌)) v)
  tgt_eq := by
    have h := (intervalFunctorVertexTypedEdge
      ((unitCommaArrow G).app (Opposite.op ⦋0⦌) v)).tgt_eq
    exact h.trans (ConcreteCategory.congr_hom
      (NatTrans.congr_app (unitCommaArrow_evaluate_one G) (Opposite.op ⦋0⦌)) v)

/-- 概要：comma の指定辺の Yoneda 表示は頂点の元の区間図式。
方針：区間頂点の辺の公式と零単体表示の両逆。
規約：一単体そのものの一致。
使われ方：合成三角形の後辺を元の comma の矢印に認識する。 -/
lemma unitCommaVertexEdge_yoneda {X Y : SSet.{u}} (G : Y ⟶ X)
    (v : (unitComma G) _⦋0⦌) :
    SSet.yonedaEquiv.symm (unitCommaVertexEdge G v).edge = unitCommaVertexArrow G v := by
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  change intervalFunctorVertexEdge _ = SSet.yonedaEquiv (unitCommaVertexArrow G v)
  rw [← unitCommaVertexArrow_functorVertex G v, intervalFunctorVertexEdge_functorVertex]

end SerrePositivity.InfinityCategories
