module
public import SerrePositivity.InfinityCategories.Derived.TriangleAppendKnownFaces
public import SerrePositivity.InfinityCategories.Core.JoinSimplexInclusions

/-! # 後合成比較三単体の最後の辺

概要：比較三単体の最後の二頂点への制限は後合成した鎖写像の辺そのもの。
方針：既知の零面から頂点と辺を回収し、一単体の外延性を使う。
規約：元の終域・新しい終域を保持する。使われ方：D7 の coslice 辺の射影。
-/
@[expose] public section
open CategoryTheory SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.DGNerve
open CochainComplex HomComplex
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
variable {S : Type u} [CommRing S] {W X Y Z : Complex S}
namespace SerrePositivity.InfinityCategories
/-- 比較三単体の最後の辺は後合成射の辺。 -/
lemma complexTriangleAppend_lastEdge (a : W ⟶ X) (b : X ⟶ Y) (c : W ⟶ Y) (t : Cochain W Y (-1))
    (ht : δ (-1) 0 t = Cochain.ofHom (a ≫ b) - Cochain.ofHom c) (q : Y ⟶ Z) :
    (complexTriangleAppend a b c t ht q).pullback (joinRightOrderHom 1 1) =
      (complexEdge q).edge := by
  let σ := complexTriangleAppend a b c t ht q
  have h0 := complexTriangleAppend_face_zero a b c t ht q
  apply dgSimplex1_ext
  · funext i
    fin_cases i
    · exact dgTetrahedron_face_obj σ 0 _ h0 1
    · exact dgTetrahedron_face_obj σ 0 _ h0 2
  · have he := SimplexData.edgeHom_heq_of_pullback_eq σ.toSimplexData
      (σ.toSimplexData.pullback (joinRightOrderHom 1 1)) (joinRightOrderHom 1 1)
      (by
        intro i j hij
        apply Fin.ext
        have hh := congrArg (fun k : Fin 4 => k.val) hij
        change 2 + i.val = 2 + j.val at hh
        omega) rfl 0 1 (by decide) (by decide)
    exact he.symm.trans (dgTetrahedron_face_edge σ 0 _ h0 1 2 (by decide))

end SerrePositivity.InfinityCategories
