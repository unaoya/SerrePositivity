module
public import SerrePositivity.InfinityCategories.Derived.ContractingPinchedHom
public import SerrePositivity.InfinityCategories.Core.TerminalMappingSpace

/-! # 収縮元を持つ dg 対象の終対象性

概要：収縮対象は dg nerve の実際の終対象となる。
方針：任意の頂点を dg 対象で表示し、入ってくる pinched Hom の全境界充填を使う。
規約：h の終対象性だけによる判定ではない。使われ方：β3 の指定対象の零化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 収縮元を持つ dg 対象の頂点は、dg nerve の終対象。 -/
lemma dgNerve_contractingElement_isTerminalVertex (y : D) (h : GradedHom A y y (-1))
    (dh : (homObject A D y y).d (-1) 0 h = (unitElement A y).val) :
    IsTerminalVertex (X := dgNerve A D) (Simplex.vertex y) := by
  apply isTerminalVertex_of_pinchedHom_isContractibleKan
  intro z
  obtain ⟨x, rfl⟩ := Simplex.vertexEquiv.symm.surjective z
  change IsContractibleKan (DGNerve.pinchedHom A D x y)
  exact contractingTargetPinchedHom_isContractibleKan h dh

end SerrePositivity.InfinityCategories
