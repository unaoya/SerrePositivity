module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SuspensionObjectComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ChainMapEdge

/-! # 通常の h D(S) の比較による鎖写像の像

概要：D3 比較で鎖写像の辺の類を送る操作は、通常の局所化 Q の作用と両立する。
方針：H⁰ 比較を代表元で計算し、Qh と Q の標準自然同型を使う。
規約：通常の道の商による h を使う。使われ方：D7 の suspension 比較の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (S : Type u) [CommRing S] [HasDerivedCategory.{w} (ModuleCat.{u} S)]

/-- D3 の通常の h の比較は鎖写像上で Q と標準同型の下で一致する。 -/
lemma derivedStableHomotopyEquivalenceVertexIso_naturality {X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S}
    (a : X.val ⟶ Y.val) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalence S).functor.map
        (SSet.Truncated.HomotopyCategory.homMk
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedChainMapEdge (x := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) (y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y) a)) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalenceVertexIso S Y).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalenceVertexIso S X).hom ≫ DerivedCategory.Q.map a := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalence, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyBridge,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyEquivalence, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityH0Equivalence,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyCategoryBridge, CategoryTheory.Equivalence.mk, CategoryTheory.Equivalence.trans,
    CategoryTheory.Equivalence.symm, Functor.comp_map, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.equivalence,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeDerivedEquivalence, Functor.asEquivalence, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.pathToEdgeHomotopyCategory,
    SSet.Truncated.HomotopyCategory.lift_map_homMk, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.toH0_homMk]
  change DerivedCategory.Qh.map ((_root_.SerrePositivity.DifferentialGraded.complexHomotopyComparison S).map
      ((dgFullSubcategoryInclusion S (Complex S) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S)).onHomotopy.map
        ((toHomotopy S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S)).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedChainMapEdge (x := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) (y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y) a))))) ≫ _ = _
  rw [_root_.SerrePositivity.DifferentialGraded.dgFullSubcategoryInclusion_onHomotopy_map]
  change DerivedCategory.Qh.map ((_root_.SerrePositivity.DifferentialGraded.complexHomotopyComparison S).map
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.toH0 S (Complex S)).map
        (SSet.Truncated.HomotopyCategory₂.homMk
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedChainMapEdge (x := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) (y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y) a).map
            ((SSet.truncation 2).map _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion))))) ≫ _ = _
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeChainMap_quotient,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedChainMapEdge_chainMap (x := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) (y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y)]
  exact DerivedCategory.quotientCompQhIso_hom_naturality a

end SerrePositivity.InfinityCategories.Project.DerivedCategories
