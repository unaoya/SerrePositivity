module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FullInclusionHomotopyFaithful
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ChainMapEdge

/-! # 通常の h D(S) の射の鎖写像代表

概要：定値頂点間の h D(S) のすべての射を実際の鎖写像で表す。
方針：辺の代表を取り、包含後に鎖写像を読み戻して、h 上の忠実性で戻す。
規約：任意の semifree 複体。使われ方：D7 の自然性をすべての h の射へ拡張する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable {S : Type u} [CommRing S] {X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S}

/-- 通常の h D(S) の定値頂点間の射は鎖写像の辺の類で代表される。 -/
lemma derivedHomotopyHom_chainMap_surjective
    (f : (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) :
      hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S)) ⟶ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y)) :
    ∃ a : X.val ⟶ Y.val,
      SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedChainMapEdge (x := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) (y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y) a) = f := by
  let : (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion (S := S))).toFunctor.Faithful :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullInclusionHo_faithful S (Complex S) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S)
  obtain ⟨e, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _ f
  let d := e.map ((truncation 2).map _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion)
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeChainMap d, ?_⟩
  apply (hoFunctor.map _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion).toFunctor.map_injective
  apply Arrow.mk_injective
  apply SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedChainMapEdge_inclusion (x := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) (y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeChainMap d)).trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derived_complexEdge_edgeChainMap d)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
