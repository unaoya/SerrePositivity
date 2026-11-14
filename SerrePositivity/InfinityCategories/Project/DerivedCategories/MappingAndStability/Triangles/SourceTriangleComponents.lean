module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.TriangleExt
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.TruncatedEdges
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinSimplexInclusions
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DataLowDimensionalPullback

/-! # 前合成した三角形と比較三単体の成分

概要：始点への前合成で三角形の二辺とホモトピーがどう変わるかを計算する。
方針：始点を保つ単射での制限と、退化写像の有限成分を使う。
規約：dg 圏の任意次数。使われ方：D7 の比較三単体の共通面。
-/
@[expose] public section
open CategoryTheory SerrePositivity.DifferentialGraded

open CochainComplex HomComplex
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
/-- 前合成した三角形の最初の辺。 -/
lemma sourceTriangle_edge01 (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D 2) {X : D}
    (f : zeroCycles (homObject R D X (s.obj 0))) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SourcePrecomposition.simplex s f).toSimplexData.edgeHom 0 1 (by decide) =
      compose R (s.toSimplexData.edgeHom 0 1 (by decide)) f.val (zero_add 0) := rfl
/-- 前合成した三角形の対角辺。 -/
lemma sourceTriangle_edge02 (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D 2) {X : D}
    (f : zeroCycles (homObject R D X (s.obj 0))) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SourcePrecomposition.simplex s f).toSimplexData.edgeHom 0 2 (by decide) =
      compose R (s.toSimplexData.edgeHom 0 2 (by decide)) f.val (zero_add 0) := rfl
/-- 前合成した三角形のホモトピー。 -/
lemma sourceTriangle_triple (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D 2) {X : D}
    (f : zeroCycles (homObject R D X (s.obj 0))) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SourcePrecomposition.simplex s f).toSimplexData.tripleHom 0 1 2 (by decide) (by decide) =
      compose R (s.toSimplexData.tripleHom 0 1 2 (by decide) (by decide)) f.val
        (zero_add (-1)) := rfl

/-- 比較三単体の共通面は対角辺から作った比較三角形。 -/
lemma prepend_triangle_face_two (σ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D 2) {Y : D}
    (g : zeroCycles (homObject R D Y (σ.obj 0))) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.prepend σ g).pullback (SimplexCategory.δ (2 : Fin 4)).toOrderHom =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.prepend (σ.pullback (SimplexCategory.δ (1 : Fin 3)).toOrderHom) g := by
  have he : (SimplexCategory.δ (2 : Fin 4)).toOrderHom =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.extend (SimplexCategory.δ (1 : Fin 3)).toOrderHom := by
    ext i; fin_cases i <;> rfl
  let τ := σ.pullback (SimplexCategory.σ (0 : Fin 3)).toOrderHom
  have hτ : τ.pullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.extend (SimplexCategory.δ (1 : Fin 3)).toOrderHom) =
      (σ.pullback (SimplexCategory.δ (1 : Fin 3)).toOrderHom).pullback
        (SimplexCategory.σ (0 : Fin 2)).toOrderHom := by
    rw [← he]
    dsimp only [τ]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_comp]
    congr 1
    ext i; fin_cases i <;> rfl
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SourcePrecomposition.simplex τ g).pullback
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.extend (SimplexCategory.δ (1 : Fin 3)).toOrderHom) :=
      congrArg (fun θ => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SourcePrecomposition.simplex τ g).pullback θ) he
    _ = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SourcePrecomposition.simplex (τ.pullback
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.extend (SimplexCategory.δ (1 : Fin 3)).toOrderHom)) g :=
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplex_pullback_extend (SimplexCategory.δ (1 : Fin 3)).toOrderHom
        (Fin.succAboveOrderEmb (1 : Fin 3)).injective τ g
    _ = _ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplex_congr hτ (heq_of_eq rfl)

/-- 単体と閉零射の等式に沿って比較単体を同定する。 -/
lemma prepend_congr {n : ℕ} {σ τ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D n} (h : σ = τ) {Y : D}
    {g : zeroCycles (homObject R D Y (σ.obj 0))}
    {g' : zeroCycles (homObject R D Y (τ.obj 0))} (hg : HEq g g') :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.prepend σ g = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.prepend τ g' := by
  cases h
  cases hg
  rfl

/-- 比較単体の最初の辺は前合成した閉零射そのもの。 -/
lemma prepend_edge01 {n : ℕ} (σ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D n) {Y : D}
    (g : zeroCycles (homObject R D Y (σ.obj 0))) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.prepend σ g).toSimplexData.edgeHom 0 1
      (by exact Fin.zero_lt_one) = g.val := by
  have hu : (σ.pullback (SimplexCategory.σ (0 : Fin (n + 1))).toOrderHom).toSimplexData.edgeHom
      0 1 (by exact Fin.zero_lt_one) = (unitElement R (σ.obj 0)).val := by
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.edgeHom
    apply eq_of_heq
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_collapsed_pair
    · intro hinj
      have hh : (0 : Fin (n + 2)) = 1 := hinj (by simp) (by simp) (by rfl)
      exact Fin.zero_ne_one hh
    · simp
  change compose (D := D) R
    ((σ.pullback (SimplexCategory.σ (0 : Fin (n + 1))).toOrderHom).toSimplexData.edgeHom
      0 1 (by exact Fin.zero_lt_one)) g.val (zero_add 0) = g.val
  rw [hu]
  exact unit_compose R g.val

/-- 比較三単体の先頭二頂点への制限は閉零射から作った辺。 -/
lemma prepend_triangle_firstEdge (σ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D 2) {Y : D}
    (g : zeroCycles (homObject R D Y (σ.obj 0))) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.prepend σ g).pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinLeftOrderHom 1 1) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pairObj Y (σ.obj 0)) g := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.edgeEquiv.injective
  apply Sigma.ext
  · funext i; fin_cases i <;> rfl
  · apply heq_of_eq
    apply Subtype.ext
    change ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.prepend σ g).pullback
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinLeftOrderHom 1 1)).toSimplexData.edgeHom
      0 1 (by decide) = g.val
    have hh := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeHom_heq_of_pullback_eq
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.prepend σ g).toSimplexData
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.prepend σ g).toSimplexData.pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinLeftOrderHom 1 1))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinLeftOrderHom 1 1)
      (by intro a b h; exact Fin.ext (congrArg (fun i : Fin 4 => i.val) h))
      rfl 0 1 (by decide) (by decide)
    exact (eq_of_heq hh).symm.trans (prepend_edge01 σ g)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
