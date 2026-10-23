module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ConstantTransformationFatDiagram
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoconeTransformationMap

/-!
概要：native な余錐の変換から作る fat join 図式を、元の余錐の表示と同定する。
方針：全円柱と固定した両端で比較する。
規約：全ての高次パラメータを保持する。
使われ方：比較射の像を厳密に固定した相対 join 延長。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：元の余錐の変換の fat join 図式は元の join 図式の標準比較による制限。
方針：円柱は全パラメータの比較式、両端は図式と頂点の固定式で照合する。
規約：厳密な射の等式。使われ方：逆を元の余錐上で恒等にする。 -/
lemma coconeTransformationFatDiagram_comparison {K X T : SSet.{u}} {f : K ⟶ X} {z : X _⦋0⦌}
    (a : T ⟶ coconeMappingSpace f z) :
    constantTransformationFatDiagram (a ≫ coconeTransformationMap f z) =
      fatJoinComparison K T ≫ sliceUnderUncurry (a ≫ vertexFiberι (sliceUnderProjection f) z) := by
  apply fatJoin_hom_ext
  · rw [constantTransformationFatDiagram_cylinder, coconeTransformationMap_prism,
      ← Category.assoc, fatJoinCylinder_comparison]
    rfl
  · rw [constantTransformationFatDiagram_inl, ← Category.assoc,
      fatJoinInl_comparison, sliceUnderUncurry_fixed]
  · rw [constantTransformationFatDiagram_inr, ← Category.assoc,
      fatJoinInr_comparison, sliceUnderUncurry_projection, Category.assoc,
      vertexFiberι_comp, SSet.comp_const]

end SerrePositivity.InfinityCategories.F2
