module

public import SerrePositivity.EInfinity.Hammock.WeakAnodyneLocalization
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.RightHomotopySquare
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.RightIntervalEquivalence

/-!
# 全パラメータの区間族の射の一致による元の pinched 族の弱同値性

概要：全関手圏内の同じ射を表す二族の片方が弱同値なら、もう片方も弱同値となる。
方針：同じ区間模型で実ホモトピーを得て、既存の pinched 比較の弱同値性で反映する。
規約：パラメータ K は任意。各頂点上の π₀ の一致を入力とはしない。
使われ方：実 ProductHomMap と元の弱な基準射の高次比較の出口。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.FrameHom
open CategoryTheory SSet SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel

lemma pinchedFamily_weak_of_intervalFamilyHom_eq {K X : SSet.{u}} [Quasicategory X]
    {x y : X.obj (Opposite.op (SimplexCategory.mk 0))} (f g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y)
    (hg : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence g)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace x y) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace x y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence f := by
  have hi := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence x y).isWeakHomotopyEquivalence
  obtain ⟨H⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom_eq_imp_homotopy h
  have he := AnodyneHomotopy.map_homotopy_eq AnodyneHomotopy.anodyneQ
    SSet.anodyneExtensions.Q_inverts H
  have hgQ := Hammock.anodyneQ_map_isIso_of_weak _ (hg.comp hi)
  have hf := AnodyneWeakDetection.isWeakHomotopyEquivalence _ (he.symm ▸ hgQ)
  exact hi.cancel_right hf

end SerrePositivity.EInfinity.FrameHom
