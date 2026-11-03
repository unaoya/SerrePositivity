module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.TetrahedronComparisonReindexRight
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeFunctorPreSplitReflection

/-!
概要：同じ四面の指定値を保つ制限に厳密な戻り射があれば、指定三関係を元の全空間へ反映する。
方針：両合成の元の指定像を同じ制限先の二合成へ同定し、指定同型への忠実性で戻す。
規約：四面と六辺の元の指定値を保持。使われ方：全選択族の係数を忘れる反映。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {X₀ X₁ X₂ X₃ Y₀ Y₁ Y₂ Y₃ : SSet.{u}}
  [Quasicategory X₀] [Quasicategory X₁] [Quasicategory X₂] [Quasicategory X₃]
  [Quasicategory Y₀] [Quasicategory Y₁] [Quasicategory Y₂] [Quasicategory Y₃]
  (D : TetrahedronComparisonReindex X₀ X₁ X₂ X₃ Y₀ Y₁ Y₂ Y₃)

/-- 厳密な戻り射を持つ制限は、同じ四面の元の指定比較の合成関係を反映する。 -/
lemma TetrahedronComparisonReindex.square_of_reindexed
    (s : Y₃ ⟶ X₃) (hs : D.r3 ≫ s = 𝟙 X₃) (x : X₀ _⦋0⦌)
    (h : D.new013.app (D.r0.app _ x) ≪≫
        D.new123.app (D.new01.app _ (D.r0.app _ x)) =
      D.new023.app (D.r0.app _ x) ≪≫
        VertexIso.map (D.new012.app (D.r0.app _ x)) D.new23) :
    D.old013.app x ≪≫ D.old123.app (D.old01.app _ x) =
      D.old023.app x ≪≫ VertexIso.map (D.old012.app x) D.old23 := by
  apply vertexIso_map_injective_of_retraction D.r3 s hs
  exact eq_of_heq ((D.left_map_heq x).trans ((heq_of_eq h).trans (D.right_map_heq x).symm))

end SerrePositivity.InfinityCategories.F2
