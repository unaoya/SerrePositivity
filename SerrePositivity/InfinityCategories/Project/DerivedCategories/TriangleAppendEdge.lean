module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.TriangleAppendKnownFaces
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinSimplexInclusions

/-! # 後合成比較三単体の最後の辺

概要：比較三単体の最後の二頂点への制限は後合成した鎖写像の辺そのもの。
方針：既知の零面から頂点と辺を回収し、一単体の外延性を使う。
規約：元の終域・新しい終域を保持する。使われ方：D7 の coslice 辺の射影。
-/
@[expose] public section
open CategoryTheory SerrePositivity.DifferentialGraded

open CochainComplex HomComplex
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
variable {S : Type u} [CommRing S] {W X Y Z : Complex S}
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
/-- 比較三単体の最後の辺は後合成射の辺。 -/
lemma complexTriangleAppend_lastEdge (a : W ⟶ X) (b : X ⟶ Y) (c : W ⟶ Y) (t : Cochain W Y (-1))
    (ht : δ (-1) 0 t = Cochain.ofHom (a ≫ b) - Cochain.ofHom c) (q : Y ⟶ Z) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexTriangleAppend a b c t ht q).pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRightOrderHom 1 1) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge q).edge := by
  let σ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexTriangleAppend a b c t ht q
  have h0 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexTriangleAppend_face_zero a b c t ht q
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
