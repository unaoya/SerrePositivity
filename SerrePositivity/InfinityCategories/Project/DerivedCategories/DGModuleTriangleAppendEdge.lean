module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleTriangleAppendKnownFaces
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinSimplexInclusions

/-! # 後合成比較三単体の最後の辺

概要：比較三単体の最後の二頂点への制限は後合成した鎖写像の辺そのもの。
方針：既知の零面から頂点と辺を回収し、一単体の外延性を使う。
規約：元の終域・新しい終域を保持する。使われ方：β3 の coslice 辺の射影。
-/
@[expose] public section
open CategoryTheory SerrePositivity.DifferentialGraded

open CochainComplex HomComplex
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {W X Y Z : ModuleCategory A D}
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
/-- 比較三単体の最後の辺は後合成射の辺。 -/
lemma dgModuleTriangleAppend_lastEdge (a : W ⟶ X) (b : X ⟶ Y) (c : W ⟶ Y)
    (t : GradedHom A (ForgetEnrichment.to (Complex A) W)
      (ForgetEnrichment.to (Complex A) Y) (-1))
    (ht : (moduleHom A D (ForgetEnrichment.to (Complex A) W)
      (ForgetEnrichment.to (Complex A) Y)).d (-1) 0 t =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (a ≫ b))).val -
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) c)).val) (q : Y ⟶ Z) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangleAppend A D a b c t ht q).pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRightOrderHom 1 1) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge A D q).edge := by
  let σ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangleAppend A D a b c t ht q
  have h0 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangleAppend_face_zero A D a b c t ht q
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplex1_ext
  · funext i
    fin_cases i
    · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTetrahedron_face_obj σ 0 _ h0 1
    · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTetrahedron_face_obj σ 0 _ h0 2
  · have he := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeHom_heq_of_pullback_eq σ.toSimplexData
      (σ.toSimplexData.pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRightOrderHom 1 1)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRightOrderHom 1 1)
      (by
        intro i j hij
        apply Fin.ext
        have hh := congrArg (fun k : Fin 4 => k.val) hij
        change 2 + i.val = 2 + j.val at hh
        omega) rfl 0 1 (by decide) (by decide)
    exact he.symm.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTetrahedron_face_edge σ 0 _ h0 1 2 (by decide))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
