module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCompositionTetrahedronDegenerateFace
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ConstantOrderDiagram

/-!
概要：合成比較三単体の初二頂点間の実辺は元の初点の恒等辺。
方針：最後の面を元の最初の辺の退化へ戻し、単体恒等式で頂点へ制限する。
規約：元の coherent 三角形と実辺を保持する。
使われ方：零面の全係数族の始点の恒等作用を計算する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 合成比較三単体の最初の実辺は、元の初点の恒等辺そのもの。 -/
lemma coherentCompositionTetrahedron_first_edge
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (s : (SimplicialNerve C) _⦋2⦌) :
    (SimplicialNerve C).δ 2 ((SimplicialNerve C).δ 3
      (coherentCompositionTetrahedron s)) =
        PinchedHom.constant (coherentNerveVertex (s.obj ⟨ULift.up 0⟩)) 1 := by
  have hf := congrArg (fun t : (SimplicialNerve C) _⦋2⦌ ↦ (SimplicialNerve C).δ 2 t)
    (coherentCompositionTetrahedron_face_three s)
  have hv : (SimplicialNerve C).δ 1 ((SimplicialNerve C).δ 2 s) =
      coherentNerveVertex (s.obj ⟨ULift.up 0⟩) := by
    apply (coherentNerveVertexEquiv C).symm.injective
    rfl
  apply hf.trans
  have h := SSet.δ_comp_σ_of_gt_apply (S := SimplicialNerve C)
    (i := (1 : Fin 2)) (j := (0 : Fin 1)) (by decide) ((SimplicialNerve C).δ 2 s)
  rw [hv] at h
  exact h

end SerrePositivity.InfinityCategories.F2
