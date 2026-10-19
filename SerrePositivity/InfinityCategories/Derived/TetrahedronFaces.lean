module
public import SerrePositivity.InfinityCategories.Derived.TetrahedronEquation
public import SerrePositivity.InfinityCategories.DGNerve.DataLowDimensionalPullback

/-! # 三単体の面からの成分の回収

概要：既知の二次元の面から頂点・辺・三点ホモトピーを取り出す。
方針：単射引き戻しの異種等号を面写像に適用する。
規約：対象の表記の差は異種等号で保持する。使われ方：D7 の比較三単体の面の同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- 指定された面の頂点は、三単体の対応する頂点。 -/
lemma dgTetrahedron_face_obj (σ : Simplex R D 3) (i : Fin 4) (τ : Simplex R D 2)
    (h : σ.pullback (SimplexCategory.δ i).toOrderHom = τ) (a : Fin 3) :
    σ.obj (i.succAbove a) = τ.obj a := congrArg (fun s : Simplex R D 2 => s.obj a) h

/-- 指定された面の辺は、三単体の対応する辺と異種等号で一致する。 -/
lemma dgTetrahedron_face_edge (σ : Simplex R D 3) (i : Fin 4) (τ : Simplex R D 2)
    (h : σ.pullback (SimplexCategory.δ i).toOrderHom = τ)
    (a b : Fin 3) (hab : a < b) :
    HEq (σ.toSimplexData.edgeHom (i.succAbove a) (i.succAbove b)
      (i.succAboveOrderEmb.strictMono hab)) (τ.toSimplexData.edgeHom a b hab) :=
  SimplexData.edgeHom_heq_of_pullback_eq σ.toSimplexData τ.toSimplexData
    (SimplexCategory.δ i).toOrderHom i.succAboveOrderEmb.injective
    (congrArg Simplex.toSimplexData h) a b hab (i.succAboveOrderEmb.strictMono hab)

/-- 指定された面のホモトピーは、三単体の対応する三点成分。 -/
lemma dgTetrahedron_face_triple (σ : Simplex R D 3) (i : Fin 4) (τ : Simplex R D 2)
    (h : σ.pullback (SimplexCategory.δ i).toOrderHom = τ) :
    HEq (σ.toSimplexData.tripleHom (i.succAbove 0) (i.succAbove 1) (i.succAbove 2)
      (i.succAboveOrderEmb.strictMono (by decide))
      (i.succAboveOrderEmb.strictMono (by decide)))
      (τ.toSimplexData.tripleHom 0 1 2 (by decide) (by decide)) :=
  SimplexData.tripleHom_heq_of_pullback_eq σ.toSimplexData τ.toSimplexData
    (SimplexCategory.δ i).toOrderHom i.succAboveOrderEmb.injective
    (congrArg Simplex.toSimplexData h) 0 1 2 (by decide) (by decide)
    (i.succAboveOrderEmb.strictMono (by decide)) (i.succAboveOrderEmb.strictMono (by decide))

/-- 最上位と二つの既知ホモトピーが零なら、残る面はホモトピーの後合成になる。 -/
lemma dgTetrahedron_missing_triple (σ : Simplex R D 3)
    (htop : σ.hom Finset.univ 0 3 (-2) (by decide) (by decide) (by decide) (by decide) = 0)
    (h₁ : σ.toSimplexData.tripleHom 0 2 3 (by decide) (by decide) = 0)
    (h₀ : σ.toSimplexData.tripleHom 1 2 3 (by decide) (by decide) = 0) :
    σ.toSimplexData.tripleHom 0 1 3 (by decide) (by decide) =
      compose R (σ.toSimplexData.edgeHom 2 3 (by decide))
        (σ.toSimplexData.tripleHom 0 1 2 (by decide) (by decide)) (add_zero (-1)) := by
  have he := σ.equation Finset.univ 0 3 (-2) (by decide) (by decide) (by decide) (by decide)
  rw [htop, show differential R 0 = 0 from map_zero _, dgSimplexData_rhs_tetrahedron,
    h₁, h₀, zero_compose, sub_zero, zero_sub] at he
  exact sub_eq_zero.mp (neg_eq_zero.mp he.symm)

end SerrePositivity.InfinityCategories
