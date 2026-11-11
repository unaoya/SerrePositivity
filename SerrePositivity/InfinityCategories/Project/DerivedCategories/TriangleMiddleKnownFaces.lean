module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.TriangleMiddleHorn
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.TetrahedronFaces
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomHEqAlgebra

/-! # 中間対象比較三単体の指定面と零成分

概要：中間対象の因子分解比較の三つの指定面と最上位成分を計算する。
方針：内部ホーンの零最上位充填と三単体の方程式を使う。
規約：零の隣接ホモトピーなら対角を挟む二つのホモトピーが等しい。
使われ方：D7 の中間対象比較の欠けた面の同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex
variable {S : Type u} [CommRing S] {A B C D : _root_.SerrePositivity.DifferentialGraded.Complex S}
variable (a : A ⟶ B) (m : B ⟶ C) (b : C ⟶ D) (c : A ⟶ D) (t : Cochain A D (-1))
variable (ht : δ (-1) 0 t = Cochain.ofHom ((a ≫ m) ≫ b) - Cochain.ofHom c)

/-- 面 0 は後ろの二射の厳密三角形。 -/
lemma complexTriangleMiddle_face_zero :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexTriangleMiddle a m b c t ht).pullback (SimplexCategory.δ (0 : Fin 4)).toOrderHom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.strictComplexTriangle m b).simplex :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexTriangleMiddle_face a m b c t ht 0 (by decide)).trans
    (SSet.yonedaEquiv.apply_symm_apply _)

/-- 面 1 は中間対象を変更した三角形。 -/
lemma complexTriangleMiddle_face_one :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexTriangleMiddle a m b c t ht).pullback (SimplexCategory.δ (1 : Fin 4)).toOrderHom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexCompStruct (a ≫ m) b c t ht).simplex :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexTriangleMiddle_face a m b c t ht 1 (by decide)).trans
    (SSet.yonedaEquiv.apply_symm_apply _)

/-- 面 3 は前の二射の厳密三角形。 -/
lemma complexTriangleMiddle_face_three :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexTriangleMiddle a m b c t ht).pullback (SimplexCategory.δ (3 : Fin 4)).toOrderHom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.strictComplexTriangle a m).simplex :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexTriangleMiddle_face a m b c t ht 3 (by decide)).trans
    (SSet.yonedaEquiv.apply_symm_apply _)

/-- 中間対象比較三単体の最上位 cochain は零。 -/
lemma complexTriangleMiddle_top_zero :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexTriangleMiddle a m b c t ht).hom Finset.univ 0 3 (-2)
      (by decide) (by decide) (by decide) (by decide) = 0 :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fillerData_top_zero _ _ _ _ _ _ _ _ _ _

/-- 最上位と両端の三点成分が零なら残る二つの三点成分は等しい。 -/
lemma dgTetrahedron_middle_triple {R : Type u} [CommRing R] {E : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
    (σ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R E 3)
    (htop : σ.hom Finset.univ 0 3 (-2) (by decide) (by decide) (by decide) (by decide) = 0)
    (h₃ : σ.toSimplexData.tripleHom 0 1 2 (by decide) (by decide) = 0)
    (h₀ : σ.toSimplexData.tripleHom 1 2 3 (by decide) (by decide) = 0) :
    σ.toSimplexData.tripleHom 0 1 3 (by decide) (by decide) =
      σ.toSimplexData.tripleHom 0 2 3 (by decide) (by decide) := by
  have he := σ.equation Finset.univ 0 3 (-2) (by decide) (by decide) (by decide) (by decide)
  rw [htop, show differential R 0 = 0 from map_zero _, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexData_rhs_tetrahedron,
    h₃, h₀, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, sub_zero, sub_zero] at he
  exact (sub_eq_zero.mp he.symm).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
