module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseFaceDomainCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseBoundaryCompatibility

/-!
概要：一次元の edgewise 境界の二面の非交差と、全正次元での面の整合性。
方針：一次元では二頂点を欠く二つの面の交わりが空であることを使い、高次元の既存の整合性とまとめる。
規約：零次元の境界充填は既存の恒等辺の構成を使う。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、右端射影の全境界に対する充填。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 概要：一次元の edgewise 境界の二面の像は交わらない。
方針：標準三単体内で二面は互いに素な頂点集合の面になることを計算する。
規約：外側の次数は一で、二面の添字は零と一。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、一次元の境界の接合で重なりの条件を消す。 -/
lemma edgewiseWeight_one_faces_inf :
    Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.{u}.map (SimplexCategory.δ (0 : Fin 2))) ⊓
      Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ (1 : Fin 2))) = ⊥ := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso_pair_face_preimage 0 0, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso_pair_face_preimage 0 1]
  change (stdSimplex.face ({_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftVertex 1 0, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex 1 0}ᶜ) ⊓
    stdSimplex.face ({_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftVertex 1 1, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex 1 1}ᶜ)).preimage
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso 1).hom = ⊥
  rw [stdSimplex.face_inter_face]
  have h : ({_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftVertex 1 0, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex 1 0}ᶜ : Finset (Fin 4)) ⊓
      {_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftVertex 1 1, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex 1 1}ᶜ = ∅ := by decide
  rw [h, stdSimplex.face_empty]
  rfl

/-- 概要：一次元の境界の各面から得た図式は同じ重みの単体を表す際に一致する。
方針：同じ面では単射性を使い、異なる二面では像の非交差で場合を除く。
規約：標的 K に充填性は要求しない。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、一次元の境界の図式の接合。 -/
lemma edgewiseBoundaryOneFaces_compatible {K : SSet.{u}}
    (a : (boundary 1 : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision K)
    (i j : Fin 2) (d : SimplexCategoryᵒᵖ)
    (x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.obj ⦋0⦌).obj d)
    (hxy : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ i)).app d x =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ j)).app d y) :
    (SSet.yonedaEquiv (boundary.ι i ≫ a)).app d x =
      (SSet.yonedaEquiv (boundary.ι j ≫ a)).app d y := by
  by_cases hij : i = j
  · subst j
    have he : x = y := (mono_iff_injective
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.{u}.map (SimplexCategory.δ i)).app d)).mp inferInstance hxy
    subst y
    rfl
  · have hi : Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.{u}.map (SimplexCategory.δ i)) ⊓
        Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ j)) = ⊥ := by
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · exact edgewiseWeight_one_faces_inf
      · rw [inf_comm]
        exact edgewiseWeight_one_faces_inf
      · exact (hij rfl).elim
    have hx : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ i)).app d x ∈
        (Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ i)) ⊓
          Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ j))).obj d :=
      ⟨⟨x, rfl⟩, ⟨y, hxy.symm⟩⟩
    rw [hi] at hx
    exact hx.elim

/-- 概要：全ての正次元の境界で、各面から得た重みの図式は像の重なりで一致する。
方針：一次元の非交差と二次元以上の pullback による整合性を合わせる。
規約：全体の次数は n+1。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、全正次元の境界接合の統一した条件。 -/
lemma edgewiseBoundaryFaces_compatible_all {K : SSet.{u}} {n : ℕ}
    (a : (boundary (n + 1) : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision K)
    (i j : Fin (n + 2)) (d : SimplexCategoryᵒᵖ)
    (x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.obj ⦋n⦌).obj d)
    (hxy : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ i)).app d x =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ j)).app d y) :
    (SSet.yonedaEquiv (boundary.ι i ≫ a)).app d x =
      (SSet.yonedaEquiv (boundary.ι j ≫ a)).app d y := by
  cases n with
  | zero => exact edgewiseBoundaryOneFaces_compatible a i j d x y hxy
  | succ n => exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseBoundaryFaces_compatible a i j d x y hxy

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
