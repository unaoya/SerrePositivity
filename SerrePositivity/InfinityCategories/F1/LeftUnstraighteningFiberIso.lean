module

public import SerrePositivity.InfinityCategories.Core.VertexFiberPullback
public import SerrePositivity.InfinityCategories.F1.LeftUnstraightening

/-!
概要：引き戻しの頂点 fiber と元の対応する頂点 fiber の同型。
方針：第一射影で写し、逆を元の fiber と定値の底の成分の組で作る。
規約：fibration 性や quasicategory 性を仮定しない。
使われ方：Kerodon Remark 5.6.2.5、Example 5.6.2.9、unstraightening の fiber 比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：𝒮 値の unstraightening の fiber は pointed space の対応する fiber と同型。
方針：pointed space の射影の引き戻しに一般の fiber 同型を適用する。
規約：元の Kan 複体との同値は後続で別に構成する。
使われ方：Kerodon Example 5.6.2.9、unstraightening の fiber の値の比較の第一段階。 -/
noncomputable def leftUnstraighteningFiberIso {C : SSet.{u + 1}}
    (F : C ⟶ SpaceInfinity.{u}) (c : C _⦋0⦌) :
    vertexFiber (leftUnstraighteningProjection F) c ≅
      vertexFiber pointedSpaceProjection (F.app (Opposite.op ⦋0⦌) c) :=
  vertexFiberPullbackIso pointedSpaceProjection F c

end SerrePositivity.InfinityCategories
