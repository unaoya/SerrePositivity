module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.FullInclusionHomotopyObjects
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.ChainMapEdge
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ArrowFaithfulReflection

/-! # 包含後の辺から鎖写像の h の類を反映する

概要：端点表示を含む辺の類を、全複体への包含後の一単体から同定する。
方針：包含の忠実性と対象での単射性を使う。
規約：元の辺の端点を保持する。使われ方：D7 の標準列の第一・第二射。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes
open _root_.CategoryTheory _root_.SerrePositivity.DifferentialGraded _root_.SSet
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S]

/-- 包含後に鎖写像の辺と一致する辺は、h 上でもその鎖写像の類になる。 -/
lemma derived_homMk_arrow_eq_of_inclusion
    {x y : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S) _⦋0⦌} {X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S}
    (e : Truncated.Edge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S)) x y)
    (a : X.val ⟶ Y.val)
    (he : (e.map ((SSet.truncation 2).map _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion)).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge a).edge) :
    Arrow.mk (Truncated.HomotopyCategory.homMk e) =
      Arrow.mk (Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedChainMapEdge (x := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) (y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y) a)) := by
  let : (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion (S := S))).toFunctor.Faithful :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullInclusionHo_faithful S (Complex S) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S)
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.arrowMk_eq_of_faithful_map (hoFunctor.map _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion).toFunctor
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullInclusionHo_obj_injective S (Complex S) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S))
  apply Truncated.HomotopyCategory.congr_arrowMk_homMk
  exact he.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedChainMapEdge_inclusion
    (x := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) (y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y) a).symm

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.3.2.2" (partial := special) "仮定：可換環上の dg 圏または加群複体（Lean が強い：任意の加法圏ではない）。結論：dg nerve の辺を閉次数 0 射と同定し、h の Hom を H⁰ と比べ、具体的な鎖写像を辺に対応させる（加群複体で一致）。"] _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.derived_homMk_arrow_eq_of_inclusion
