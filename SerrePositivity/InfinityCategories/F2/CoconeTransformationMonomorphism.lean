module

public import SerrePositivity.InfinityCategories.F2.CoconeTransformationMap
public import SerrePositivity.InfinityCategories.Core.FatJoinComparisonEpi

/-!
概要：native な余錐から定値変換空間への標準比較は単射。
方針：全円柱と固定した両端から fat join 図式を復元し、比較のエピ性で元へ戻す。
規約：形状の非空性や標的の充填性は不要。
使われ方：固定した部分族を保つ比較の逆の構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：余錐空間への射は全円柱表示で一意に決まる。
方針：fat join の円柱・両端の外延性と比較のエピ性を使う。
規約：全てのパラメータで成立。使われ方：余錐から変換空間への比較の単射性。 -/
lemma coconeParameterPrism_injective {K X T : SSet.{u}} {f : K ⟶ X} {z : X _⦋0⦌} :
    Function.Injective (coconeParameterPrism (T := T) (f := f) (z := z)) := by
  intro a b h
  apply vertexFiber_hom_ext (sliceUnderProjection f) z
  apply sliceUnderUncurry_injective f
  apply (cancel_epi (fatJoinComparison K T)).mp
  apply fatJoin_hom_ext
  · rw [← Category.assoc, fatJoinCylinder_comparison,
      ← Category.assoc, fatJoinCylinder_comparison]
    exact h
  · rw [← Category.assoc, fatJoinInl_comparison, sliceUnderUncurry_fixed,
      ← Category.assoc, fatJoinInl_comparison, sliceUnderUncurry_fixed]
  · rw [← Category.assoc, fatJoinInr_comparison, sliceUnderUncurry_projection,
      ← Category.assoc, fatJoinInr_comparison, sliceUnderUncurry_projection,
      Category.assoc, vertexFiberι_comp, Category.assoc, vertexFiberι_comp,
      SSet.comp_const, SSet.comp_const]

/-- 概要：native な余錐空間から定値変換空間への標準比較は単射。
方針：比較後に一致する族の円柱を同定し、元の余錐の族を復元する。
規約：標的の quasicategory 性は不要。使われ方：相対的な比較の構成。 -/
instance coconeTransformationMap_mono {K X : SSet.{u}} (f : K ⟶ X) (z : X _⦋0⦌) :
    Mono (coconeTransformationMap f z) where
  right_cancellation {T} a b h := by
    apply coconeParameterPrism_injective
    rw [← coconeTransformationMap_prism a, ← coconeTransformationMap_prism b, h]

end SerrePositivity.InfinityCategories.F2
