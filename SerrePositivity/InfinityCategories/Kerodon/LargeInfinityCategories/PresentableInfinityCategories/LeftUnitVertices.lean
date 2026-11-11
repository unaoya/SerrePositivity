module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LeftUnitInvariance

/-!
概要：元の随伴の実単位を、固定左の全関手圏の coslice に持ち上げる。
方針：同じ代表辺を coslice 頂点として引き戻し、単位の回収を検証する。
規約：右関手の保存条件を追加の仮定にしない。
使われ方：普遍単位の空間と随伴条件の比較の基準頂点。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：固定左関手との元の随伴の実単位を coslice 頂点へ持ち上げる。
方針：指定単位の代表辺と右関手の頂点を引き戻す。
規約：元の左右の関手と指定単位を使う。
使われ方：随伴単位の条件を満たす基準頂点。 -/
def leftUnitVertex {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    {w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D _⦋0⦌} {R : D.obj ⟶ C.obj}
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftVertexFunctor w) R) : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LeftUnitCoslice C D w _⦋0⦌ :=
  SSet.yonedaEquiv (pullback.lift (SSet.yonedaEquiv.symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.edgeCosliceVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy a.unitHom))))
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex R)) (by
      rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.edgeCosliceVertex_projection]
      rfl))

/-- 概要：指定随伴からの頂点の単位の coslice 成分は元の代表辺。
方針：引き戻しの第一射影と Yoneda の往復を計算する。
規約：一次単体の代表を保つ。
使われ方：元の指定単位の回収。 -/
lemma leftUnitVertex_slice {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    {w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D _⦋0⦌} {R : D.obj ⟶ C.obj}
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftVertexFunctor w) R) :
    (pullback.fst _ ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftVertexFunctor w)).app C.obj)).app (Opposite.op ⦋0⦌)
      (leftUnitVertex a) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.edgeCosliceVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy a.unitHom)) := by
  dsimp only [leftUnitVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LeftUnitCoslice]
  rw [← SSet.yonedaEquiv_comp, pullback.lift_fst, Equiv.apply_symm_apply]

/-- 概要：指定随伴からの頂点の右関手の頂点は元の右関手。
方針：引き戻しの第二射影と Yoneda の往復を計算する。
規約：元の関手頂点の厳密な回収。
使われ方：単位の随伴条件の端点の照合。 -/
lemma leftUnitVertex_base {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    {w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D _⦋0⦌} {R : D.obj ⟶ C.obj}
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftVertexFunctor w) R) :
    (pullback.snd _ ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftVertexFunctor w)).app C.obj)).app (Opposite.op ⦋0⦌)
      (leftUnitVertex a) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex R := by
  dsimp only [leftUnitVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LeftUnitCoslice]
  rw [← SSet.yonedaEquiv_comp, pullback.lift_snd, Equiv.apply_symm_apply]

/-- 概要：指定随伴からの頂点の右関手は元の右関手。
方針：底の頂点の計算を関手頂点の表示の逆に移す。
規約：元の単体集合の射として等しい。
使われ方：単位条件の輸送。 -/
lemma leftUnitVertex_right {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    {w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D _⦋0⦌} {R : D.obj ⟶ C.obj}
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftVertexFunctor w) R) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftUnitRightFunctor (leftUnitVertex a) = R := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftUnitRightFunctor
  rw [leftUnitVertex_base]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv D.obj C.obj).symm_apply_apply R

/-- 概要：指定随伴からの頂点の単位の一次単体は元の代表辺。
方針：coslice 成分の回収と辺の coslice 表示の往復を使う。
規約：端点の正規化以外に単位を変更しない。
使われ方：指定単位の写像空間条件を持ち上げる。 -/
lemma leftUnitVertex_edge {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    {w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D _⦋0⦌} {R : D.obj ⟶ C.obj}
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftVertexFunctor w) R) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftUnitEdge (leftUnitVertex a)).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy a.unitHom)).edge := by
  exact (congrArg (fun s ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 C.obj)) s).edge)
    (leftUnitVertex_slice a)).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitCosliceEdge_roundtrip _)

/-- 概要：指定随伴の持ち上げは元の単位の随伴条件を満たす。
方針：同じ代表辺の Hom 類を回収し、元の単位条件を端点の等式で移す。
規約：元の指定単位を保ち、任意の随伴単位を選び直さない。
使われ方：随伴単位の全部分空間の基準頂点。 -/
lemma leftUnitVertex_condition {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    {w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D _⦋0⦌} {R : D.obj ⟶ C.obj}
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftVertexFunctor w) R) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition (F := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftVertexFunctor w)
      (G := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftUnitRightFunctor (leftUnitVertex a)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftUnitHom (leftUnitVertex a)) := by
  have he : HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftUnitHom (leftUnitVertex a)) a.unitHom :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.edgeHom_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftUnitEdge (leftUnitVertex a))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy a.unitHom))
      (leftUnitVertex_edge a)).trans
      (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy_hom a.unitHom))
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitCondition_transport rfl (leftUnitVertex_right a)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftUnitHom (leftUnitVertex a)) a.unitHom he).mpr a.unitMappingSpaceCondition

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
