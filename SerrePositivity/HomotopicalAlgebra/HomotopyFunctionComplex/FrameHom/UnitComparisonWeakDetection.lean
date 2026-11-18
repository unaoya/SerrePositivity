module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.PinchedFamilyWeakDetection

/-!
# 弱な probe の全族比較から元の単位比較への弱同値性の反映

概要：元の区間写像を弱な probe で調べ、同じ全族を表す弱な pinched 基準射から反映する。
方針：全 h Fun の射の一致を実ホモトピーに戻し、anodyne 局所化と二対三則を使う。
規約：検査対象の射自身の弱同値性や各頂点上だけの一致は仮定しない。
使われ方：標準単位比較に元の全要素族を代入する際の、Derived に依存しない最終判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
open _root_.CategoryTheory _root_.SSet _root_.SerrePositivity.InfinityCategories _root_.SerrePositivity.SimplicialModel

/-- 概要：弱な probe 上の全区間族比較は、元の比較射自身の弱同値性を与える。
方針：基準 pinched 族との実ホモトピーで前合成の弱同値性を得て probe を消去する。
規約：同じパラメータ K と固定した両端を保持し、元の比較射 f を結論に残す。
使われ方：実単位の全族公式と全屋根比較を接続した後の弱同値性の出口。 -/
lemma unitComparison_weak_of_probe_family {K D X : SSet.{u}} [Quasicategory X]
    {x y : X.obj (Opposite.op (SimplexCategory.mk 0))}
    (f : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) (p : K ⟶ D) (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y)
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence p) (hg : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence g)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (p ≫ f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace x y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence f := by
  have hi := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence x y).isWeakHomotopyEquivalence
  obtain ⟨H⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom_eq_imp_homotopy h
  have he := AnodyneHomotopy.map_homotopy_eq AnodyneHomotopy.anodyneQ
    SSet.anodyneExtensions.Q_inverts H
  have hgQ := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.anodyneQ_map_isIso_of_weak _ (hg.comp hi)
  have hpf := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.isWeakHomotopyEquivalence _ (he.symm ▸ hgQ)
  exact hp.cancel_left hpf

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
