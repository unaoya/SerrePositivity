module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.UnstraighteningConstantVertices
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorSpaceCurrying

/-!
概要：元の指定変換への定値族の全空間作用を、同じ指定頂点の実際の作用で表示する。
方針：元の比較頂点の厳密な往復と定値関手頂点の展開を使う。
規約：全パラメータを保持。使われ方：元の pointed 三角形の終点を native 合成へ同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の指定変換の定値族を展開した実射は、同じ頂点の選択済み実射への後合成。 -/
lemma unstraighteningMappingConst_uncurry {B K : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u})
    (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌) :
    relativeFunctorUncurry ((SSet.const x : K ⟶ _) ≫ leftUnstraighteningMappingSpaceMap F G) =
      fst (leftUnstraightening F) K ≫ (leftUnstraighteningMappingVertexMap F G x).val := by
  rw [SSet.const_comp, relativeFunctorUncurry, SSet.const_comp]
  have hv := congrArg Subtype.val (leftUnstraighteningMappingVertexMap_vertex F G x)
  change uncurry (SSet.const
    (((leftUnstraighteningMappingSpaceMap F G).app (Opposite.op ⦋0⦌) x).val)) = _
  rw [← hv]
  change uncurry (SSet.const (functorVertex (leftUnstraighteningMappingVertexMap F G x).val)) = _
  rw [uncurry_const_functorVertex]

end SerrePositivity.InfinityCategories.F2
