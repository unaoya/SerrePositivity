module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ContractingPinchedHom
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalMappingSpace

/-! # 収縮元を持つ dg 対象の終対象性

概要：収縮対象は dg nerve の実際の終対象となる。
方針：任意の頂点を dg 対象で表示し、入ってくる pinched Hom の全境界充填を使う。
規約：h の終対象性だけによる判定ではない。使われ方：β3 の指定対象の零化。

対応節は Kerodon 4.7（Tag 05EA）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 収縮元を持つ dg 対象の頂点は、dg nerve の終対象。 -/
lemma dgNerve_contractingElement_isTerminalVertex (y : D) (h : _root_.SerrePositivity.DifferentialGraded.GradedHom A y y (-1))
    (dh : (_root_.SerrePositivity.DifferentialGraded.homObject A D y y).d (-1) 0 h = (_root_.SerrePositivity.DifferentialGraded.unitElement A y).val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isTerminalVertex_of_pinchedHom_isContractibleKan
  intro z
  obtain ⟨x, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective z
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y)
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.contractingTargetPinchedHom_isContractibleKan h dh

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
