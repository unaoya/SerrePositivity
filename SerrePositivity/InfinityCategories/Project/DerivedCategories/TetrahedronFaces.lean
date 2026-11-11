module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.TetrahedronEquation
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DataLowDimensionalPullback

/-! # 三単体の面からの成分の回収

概要：既知の二次元の面から頂点・辺・三点ホモトピーを取り出す。
方針：単射引き戻しの異種等号を面写像に適用する。
規約：対象の表記の差は異種等号で保持する。使われ方：D7 の比較三単体の面の同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]

/-- 指定された面の頂点は、三単体の対応する頂点。 -/
lemma dgTetrahedron_face_obj (σ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D 3) (i : Fin 4) (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D 2)
    (h : σ.pullback (SimplexCategory.δ i).toOrderHom = τ) (a : Fin 3) :
    σ.obj (i.succAbove a) = τ.obj a := congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D 2 => s.obj a) h

/-- 指定された面の辺は、三単体の対応する辺と異種等号で一致する。 -/
lemma dgTetrahedron_face_edge (σ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D 3) (i : Fin 4) (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D 2)
    (h : σ.pullback (SimplexCategory.δ i).toOrderHom = τ)
    (a b : Fin 3) (hab : a < b) :
    HEq (σ.toSimplexData.edgeHom (i.succAbove a) (i.succAbove b)
      (i.succAboveOrderEmb.strictMono hab)) (τ.toSimplexData.edgeHom a b hab) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeHom_heq_of_pullback_eq σ.toSimplexData τ.toSimplexData
    (SimplexCategory.δ i).toOrderHom i.succAboveOrderEmb.injective
    (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.toSimplexData h) a b hab (i.succAboveOrderEmb.strictMono hab)

/-- 指定された面のホモトピーは、三単体の対応する三点成分。 -/
lemma dgTetrahedron_face_triple (σ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D 3) (i : Fin 4) (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D 2)
    (h : σ.pullback (SimplexCategory.δ i).toOrderHom = τ) :
    HEq (σ.toSimplexData.tripleHom (i.succAbove 0) (i.succAbove 1) (i.succAbove 2)
      (i.succAboveOrderEmb.strictMono (by decide))
      (i.succAboveOrderEmb.strictMono (by decide)))
      (τ.toSimplexData.tripleHom 0 1 2 (by decide) (by decide)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.tripleHom_heq_of_pullback_eq σ.toSimplexData τ.toSimplexData
    (SimplexCategory.δ i).toOrderHom i.succAboveOrderEmb.injective
    (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.toSimplexData h) 0 1 2 (by decide) (by decide)
    (i.succAboveOrderEmb.strictMono (by decide)) (i.succAboveOrderEmb.strictMono (by decide))

/-- 最上位と二つの既知ホモトピーが零なら、残る面はホモトピーの後合成になる。 -/
lemma dgTetrahedron_missing_triple (σ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D 3)
    (htop : σ.hom Finset.univ 0 3 (-2) (by decide) (by decide) (by decide) (by decide) = 0)
    (h₁ : σ.toSimplexData.tripleHom 0 2 3 (by decide) (by decide) = 0)
    (h₀ : σ.toSimplexData.tripleHom 1 2 3 (by decide) (by decide) = 0) :
    σ.toSimplexData.tripleHom 0 1 3 (by decide) (by decide) =
      _root_.SerrePositivity.DifferentialGraded.compose R (σ.toSimplexData.edgeHom 2 3 (by decide))
        (σ.toSimplexData.tripleHom 0 1 2 (by decide) (by decide)) (add_zero (-1)) := by
  have he := σ.equation Finset.univ 0 3 (-2) (by decide) (by decide) (by decide) (by decide)
  rw [htop, show differential R 0 = 0 from map_zero _, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexData_rhs_tetrahedron,
    h₁, h₀, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, sub_zero, zero_sub] at he
  exact sub_eq_zero.mp (neg_eq_zero.mp he.symm)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
