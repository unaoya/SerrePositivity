module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.TetrahedronComparisonReindexLeft

/-!
概要：右側の指定合成も、後合成を含めて同じ制限先の指定合成へ移る。
方針：相対制限と最後の辺の厳密な可換性で、三角形の後合成の指定値を交換する。
規約：元の指定値と端点等式を保持。使われ方：三関係の元の全空間への反映。
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

/-- 元の最後の辺による後合成を写した値は、同じ制限先の後合成の指定値。 -/
lemma TetrahedronComparisonReindex.whisker_map_heq (x : X₀ _⦋0⦌) :
    HEq (VertexIso.map (VertexIso.map (D.old012.app x) D.old23) D.r3)
      (VertexIso.map (D.new012.app (D.r0.app _ x)) D.new23) := by
  have ha := congrArg (fun f : X₀ ⟶ Y₂ => f.app (Opposite.op ⦋0⦌) x) D.comm02.w
  have hb := congrArg (fun f : X₀ ⟶ Y₂ => f.app (Opposite.op ⦋0⦌) x)
    (D.comm01.horiz_comp D.comm12).w
  have hm := vertexIso_map_heq_of_heq (VertexIso.map (D.old012.app x) D.r2)
    (D.new012.app (D.r0.app _ x)) ha hb (D.value012 x) D.new23
  exact (heq_of_eq (vertexIso_map_comp _ D.old23 D.r3)).trans
    ((vertexIso_map_heq _ D.comm23.w).trans
      ((heq_of_eq (vertexIso_map_comp _ D.r2 D.new23).symm).trans hm))

/-- 元の右側の指定合成を写した値は、制限先の同じ二面の指定合成の値。 -/
lemma TetrahedronComparisonReindex.right_map_heq (x : X₀ _⦋0⦌) :
    HEq (VertexIso.map (D.old023.app x ≪≫ VertexIso.map (D.old012.app x) D.old23) D.r3)
      (D.new023.app (D.r0.app _ x) ≪≫
        VertexIso.map (D.new012.app (D.r0.app _ x)) D.new23) := by
  have ha := congrArg (fun f : X₀ ⟶ Y₃ => f.app (Opposite.op ⦋0⦌) x) D.comm03.w
  have hb := congrArg (fun f : X₀ ⟶ Y₃ => f.app (Opposite.op ⦋0⦌) x)
    (D.comm02.horiz_comp D.comm23).w
  have hd := congrArg (fun f : X₀ ⟶ Y₃ => f.app (Opposite.op ⦋0⦌) x)
    ((D.comm01.horiz_comp D.comm12).horiz_comp D.comm23).w
  have h := vertexIso_trans_heq_of_heq
    (VertexIso.map (D.old023.app x) D.r3)
    (VertexIso.map (VertexIso.map (D.old012.app x) D.old23) D.r3)
    (D.new023.app (D.r0.app _ x))
    (VertexIso.map (D.new012.app (D.r0.app _ x)) D.new23)
    ha hb hd (D.value023 x) (D.whisker_map_heq x)
  exact (heq_of_eq (vertexIso_map_trans _ _ D.r3)).trans h

end SerrePositivity.InfinityCategories.F2
