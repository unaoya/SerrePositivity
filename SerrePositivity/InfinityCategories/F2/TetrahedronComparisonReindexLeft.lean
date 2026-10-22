module

public import SerrePositivity.InfinityCategories.F2.TetrahedronComparisonReindex

/-!
概要：二面の左側の合成は、六辺の制限と四面の元の指定自然性を保って移る。
方針：共有頂点の厳密な等式で指定同型の合成を輸送する。
規約：元の指定値を保持。使われ方：三関係を切断で元の全空間へ反映する。
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

/-- 元の左側の指定合成を写した値は、制限先の同じ二面の指定合成の値。 -/
lemma TetrahedronComparisonReindex.left_map_heq (x : X₀ _⦋0⦌) :
    HEq (VertexIso.map (D.old013.app x ≪≫ D.old123.app (D.old01.app _ x)) D.r3)
      (D.new013.app (D.r0.app _ x) ≪≫ D.new123.app (D.new01.app _ (D.r0.app _ x))) := by
  have ha := congrArg (fun f : X₀ ⟶ Y₃ => f.app (Opposite.op ⦋0⦌) x) D.comm03.w
  have hb := congrArg (fun f : X₀ ⟶ Y₃ => f.app (Opposite.op ⦋0⦌) x)
    (D.comm01.horiz_comp D.comm13).w
  have hd := congrArg (fun f : X₀ ⟶ Y₃ => f.app (Opposite.op ⦋0⦌) x)
    ((D.comm01.horiz_comp D.comm12).horiz_comp D.comm23).w
  have hx := congrArg (fun f : X₀ ⟶ Y₁ => f.app (Opposite.op ⦋0⦌) x) D.comm01.w
  have hg := (D.value123 (D.old01.app _ x)).trans
    (functorIso_app_heq_of_vertex_eq D.new123 hx)
  have h := vertexIso_trans_heq_of_heq
    (VertexIso.map (D.old013.app x) D.r3)
    (VertexIso.map (D.old123.app (D.old01.app _ x)) D.r3)
    (D.new013.app (D.r0.app _ x)) (D.new123.app (D.new01.app _ (D.r0.app _ x)))
    ha hb hd (D.value013 x) hg
  exact (heq_of_eq (vertexIso_map_trans _ _ D.r3)).trans h

end SerrePositivity.InfinityCategories.F2
