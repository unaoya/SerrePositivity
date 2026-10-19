module
public import SerrePositivity.InfinityCategories.Derived.TriangleMiddleKnownFaces

/-! # 中間対象比較の欠けた面の同定

概要：零最上位充填の面 2 は元の中間対象を経由する三角形。
方針：指定面から各辺を回収し、三単体方程式で三点ホモトピーを同定する。
規約：二つの面は同じ次数 −1 cochain を保持する。使われ方：D7 の三角形のホモトピー。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve CochainComplex HomComplex
variable {S : Type u} [CommRing S] {A B C D : Complex S}
variable (a : A ⟶ B) (m : B ⟶ C) (b : C ⟶ D) (c : A ⟶ D) (t : Cochain A D (-1))
variable (ht : δ (-1) 0 t = Cochain.ofHom ((a ≫ m) ≫ b) - Cochain.ofHom c)

include ht

/-- 因子分解前の中間対象を経由する三角形の微分式。 -/
lemma complexTriangleMiddle_sourceEquation :
    δ (-1) 0 t = Cochain.ofHom (a ≫ (m ≫ b)) - Cochain.ofHom c := by
  simpa only [Category.assoc] using ht

/-- 面 2 は因子分解前の三角形とホモトピーを厳密に保つ。 -/
lemma complexTriangleMiddle_face_two :
    (complexTriangleMiddle a m b c t ht).pullback (SimplexCategory.δ (2 : Fin 4)).toOrderHom =
      (complexCompStruct a (m ≫ b) c t
        (complexTriangleMiddle_sourceEquation a m b c t ht)).simplex := by
  let σ := complexTriangleMiddle a m b c t ht
  have h0 := complexTriangleMiddle_face_zero a m b c t ht
  have h1 := complexTriangleMiddle_face_one a m b c t ht
  have h3 := complexTriangleMiddle_face_three a m b c t ht
  have hx0 : σ.obj 0 = A := dgTetrahedron_face_obj σ 1 _ h1 0
  have hx1 : σ.obj 1 = B := dgTetrahedron_face_obj σ 3 _ h3 1
  have hx2 : σ.obj 2 = C := dgTetrahedron_face_obj σ 1 _ h1 1
  have hx3 : σ.obj 3 = D := dgTetrahedron_face_obj σ 1 _ h1 2
  have he01 : HEq (σ.toSimplexData.edgeHom 0 1 (by decide)) (Cochain.ofHom a) :=
    dgTetrahedron_face_edge σ 3 _ h3 0 1 (by decide)
  have he13 : HEq (σ.toSimplexData.edgeHom 1 3 (by decide)) (Cochain.ofHom (m ≫ b)) :=
    dgTetrahedron_face_edge σ 0 _ h0 0 2 (by decide)
  have he03 : HEq (σ.toSimplexData.edgeHom 0 3 (by decide)) (Cochain.ofHom c) :=
    dgTetrahedron_face_edge σ 1 _ h1 0 2 (by decide)
  have ht012 : HEq (σ.toSimplexData.tripleHom 0 1 2 (by decide) (by decide))
      (0 : Cochain A C (-1)) := dgTetrahedron_face_triple σ 3 _ h3
  have ht123 : HEq (σ.toSimplexData.tripleHom 1 2 3 (by decide) (by decide))
      (0 : Cochain B D (-1)) := dgTetrahedron_face_triple σ 0 _ h0
  have ht023 : HEq (σ.toSimplexData.tripleHom 0 2 3 (by decide) (by decide)) t :=
    dgTetrahedron_face_triple σ 1 _ h1
  have hz012 : σ.toSimplexData.tripleHom 0 1 2 (by decide) (by decide) = 0 :=
    eq_of_heq (ht012.trans (gradedHom_zero_heq (A := S) (D := Complex S)
      (k := (-1)) (l := (-1)) hx0 hx2 rfl).symm)
  have hz123 : σ.toSimplexData.tripleHom 1 2 3 (by decide) (by decide) = 0 :=
    eq_of_heq (ht123.trans (gradedHom_zero_heq (A := S) (D := Complex S)
      (k := (-1)) (l := (-1)) hx1 hx3 rfl).symm)
  have ht013 := (heq_of_eq (dgTetrahedron_middle_triple σ
    (complexTriangleMiddle_top_zero a m b c t ht) hz012 hz123)).trans ht023
  apply dgSimplex2_ext
  · funext i
    fin_cases i
    · exact hx0
    · exact hx1
    · exact hx3
  · exact (dgTetrahedron_face_edge σ 2 _ rfl 0 1 (by decide)).symm.trans he01
  · exact (dgTetrahedron_face_edge σ 2 _ rfl 1 2 (by decide)).symm.trans he13
  · exact (dgTetrahedron_face_edge σ 2 _ rfl 0 2 (by decide)).symm.trans he03
  · exact (dgTetrahedron_face_triple σ 2 _ rfl).symm.trans ht013

end SerrePositivity.InfinityCategories
