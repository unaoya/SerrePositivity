module
public import SerrePositivity.InfinityCategories.Derived.SuspensionObjectComparison
public import SerrePositivity.InfinityCategories.Derived.ChainMapEdge

/-! # 通常の h D(S) の比較による鎖写像の像

概要：D3 比較で鎖写像の辺の類を送る操作は、通常の局所化 Q の作用と両立する。
方針：H⁰ 比較を代表元で計算し、Qh と Q の標準自然同型を使う。
規約：通常の道の商による h を使う。使われ方：D7 の suspension 比較の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (S : Type u) [CommRing S] [HasDerivedCategory.{w} (ModuleCat.{u} S)]

/-- D3 の通常の h の比較は鎖写像上で Q と標準同型の下で一致する。 -/
lemma derivedStableHomotopyEquivalenceVertexIso_naturality {X Y : Semifree S}
    (a : X.val ⟶ Y.val) :
    (derivedStableHomotopyEquivalence S).functor.map
        (SSet.Truncated.HomotopyCategory.homMk
          (derivedChainMapEdge (x := Simplex.vertex X) (y := Simplex.vertex Y) a)) ≫
      (derivedStableHomotopyEquivalenceVertexIso S Y).hom =
    (derivedStableHomotopyEquivalenceVertexIso S X).hom ≫ DerivedCategory.Q.map a := by
  simp only [derivedStableHomotopyEquivalence, derivedStableHomotopyBridge,
    derivedInfinityHomotopyEquivalence, derivedInfinityH0Equivalence,
    homotopyCategoryBridge, CategoryTheory.Equivalence.mk, CategoryTheory.Equivalence.trans,
    CategoryTheory.Equivalence.symm, Functor.comp_map, DGNerve.HomotopyComparison.equivalence,
    semifreeDerivedEquivalence, Functor.asEquivalence, pathToEdgeHomotopyCategory,
    SSet.Truncated.HomotopyCategory.lift_map_homMk, DGNerve.HomotopyComparison.toH0_homMk]
  change DerivedCategory.Qh.map ((complexHomotopyComparison S).map
      ((dgFullSubcategoryInclusion S (Complex S) (complexSemifree S)).onHomotopy.map
        ((toHomotopy S (Semifree S)).map (HomotopyComparison.edgeClosed
          (derivedChainMapEdge (x := Simplex.vertex X) (y := Simplex.vertex Y) a))))) ≫ _ = _
  rw [dgFullSubcategoryInclusion_onHomotopy_map]
  change DerivedCategory.Qh.map ((complexHomotopyComparison S).map
      ((HomotopyComparison.toH0 S (Complex S)).map
        (SSet.Truncated.HomotopyCategory₂.homMk
          ((derivedChainMapEdge (x := Simplex.vertex X) (y := Simplex.vertex Y) a).map
            ((SSet.truncation 2).map derivedInfinityInclusion))))) ≫ _ = _
  rw [← edgeChainMap_quotient,
    derivedChainMapEdge_chainMap (x := Simplex.vertex X) (y := Simplex.vertex Y)]
  exact DerivedCategory.quotientCompQhIso_hom_naturality a

end SerrePositivity.InfinityCategories
