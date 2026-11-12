module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaFamilies
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianPathSpace

/-!
概要：comma の矢印射影の二つの端点を始域・標的の射影で回収する。
方針：区間図式の uncurry の端点公式を評価射で表す。
規約：単位の選択や quasicategory 性は不要。
使われ方：B1 の標的を固定した cartesian lift の端点の認識。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 概要：comma の矢印の始点評価は始域射影。
方針：展開した矢印の零端点公式を使う。
規約：射として厳密に一致する。
使われ方：cartesian lift の始域の照合。 -/
lemma unitCommaArrow_evaluate_zero {X Y : SSet.{u}} (G : Y ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaArrow G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaUncurry_zero (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComma G))
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaArrow G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComma G) ≫ uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaArrow G) := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro v
    rfl
  rw [he]
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaUncurry, Category.id_comp] using h

/-- 概要：comma の矢印の終点評価は標的射影の後の G。
方針：展開した矢印の一端点公式を使う。
規約：射として厳密に一致する。
使われ方：標的を固定した lift の矢印の端点の照合。 -/
lemma unitCommaArrow_evaluate_one {X Y : SSet.{u}} (G : Y ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaArrow G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget G ≫ G := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaUncurry_one (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComma G))
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaArrow G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComma G) ≫ uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaArrow G) := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro v
    rfl
  rw [he]
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaUncurry, Category.id_comp] using h

/-- 概要：comma の頂点の矢印を X の実際の区間図式にする。
方針：矢印射影の頂点に内部 Hom の零単体表示同値を適用する。
規約：ホモトピー類から新しい代表を選ばない。
使われ方：cartesian lift の合成三角形に渡す指定辺。 -/
noncomputable def unitCommaVertexArrow {X Y : SSet.{u}} (G : Y ⟶ X)
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComma G) _⦋0⦌) : (Δ[1] : SSet.{u}) ⟶ X :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[1] X).symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaArrow G).app (Opposite.op ⦋0⦌) v)

/-- 概要：頂点の矢印表示を戻すと元の矢印射影の頂点に一致する。
方針：内部 Hom の表示同値の両逆。
規約：厳密な一致。
使われ方：lift の終点を元の comma 頂点に戻す。 -/
lemma unitCommaVertexArrow_functorVertex {X Y : SSet.{u}} (G : Y ⟶ X)
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComma G) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (unitCommaVertexArrow G v) = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaArrow G).app (Opposite.op ⦋0⦌) v :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[1] X).apply_symm_apply _

/-- 概要：comma の頂点は始域射影から G を続けた標的射影への指定辺を与える。
方針：区間頂点の辺の両端を、矢印射影の二つの評価公式で揃える。
規約：元の矢印の一単体を保持する。
使われ方：始域の辺との合成による cartesian lift の構成。 -/
noncomputable def unitCommaVertexEdge {X Y : SSet.{u}} (G : Y ⟶ X)
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComma G) _⦋0⦌) :
    SSet.Truncated.Edge (X := (truncation 2).obj X)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G).app (Opposite.op ⦋0⦌) v)
      (G.app (Opposite.op ⦋0⦌) ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget G).app (Opposite.op ⦋0⦌) v)) where
  edge := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaArrow G).app (Opposite.op ⦋0⦌) v)
  src_eq := by
    have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.intervalFunctorVertexTypedEdge
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaArrow G).app (Opposite.op ⦋0⦌) v)).src_eq
    exact h.trans (ConcreteCategory.congr_hom
      (NatTrans.congr_app (unitCommaArrow_evaluate_zero G) (Opposite.op ⦋0⦌)) v)
  tgt_eq := by
    have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.intervalFunctorVertexTypedEdge
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaArrow G).app (Opposite.op ⦋0⦌) v)).tgt_eq
    exact h.trans (ConcreteCategory.congr_hom
      (NatTrans.congr_app (unitCommaArrow_evaluate_one G) (Opposite.op ⦋0⦌)) v)

/-- 概要：comma の指定辺の Yoneda 表示は頂点の元の区間図式。
方針：区間頂点の辺の公式と零単体表示の両逆。
規約：一単体そのものの一致。
使われ方：合成三角形の後辺を元の comma の矢印に認識する。 -/
lemma unitCommaVertexEdge_yoneda {X Y : SSet.{u}} (G : Y ⟶ X)
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComma G) _⦋0⦌) :
    SSet.yonedaEquiv.symm (unitCommaVertexEdge G v).edge = unitCommaVertexArrow G v := by
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge _ = SSet.yonedaEquiv (unitCommaVertexArrow G v)
  rw [← unitCommaVertexArrow_functorVertex G v, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_functorVertex]

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
