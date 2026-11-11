module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseFacePullbacks
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseBoundaryLifting

/-!
概要：edgewise の境界の各面から得る重みの図式の重なりでの一致。
方針：境界内の二面の恒等式を Yoneda の制限へ移し、重みの pullback で任意の共通単体を比較する。
規約：ここでは二次元以上の境界の順序付けた二面を扱う。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、右射影の境界図式の接合。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 概要：標準単体の境界内でも二面の共通面の二通りの包含は等しい。
方針：境界包含の単射性で全標準単体へ写し、単体圏の面の恒等式を使う。
規約：外側の二面は i.castSucc と j.succ。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、境界図式の自然性を使う元の等式。 -/
lemma boundary_faces_overlap {n : ℕ} (i j : Fin (n + 2)) (hij : i ≤ j) :
    (stdSimplex.{u}.δ j) ≫ boundary.ι i.castSucc =
      stdSimplex.δ i ≫ boundary.ι j.succ := by
  apply (cancel_mono (boundary.{u} (n + 2)).ι).1
  simp only [Category.assoc, boundary.ι_ι]
  change stdSimplex.map (SimplexCategory.δ j) ≫ stdSimplex.map (SimplexCategory.δ i.castSucc) =
    stdSimplex.map (SimplexCategory.δ i) ≫ stdSimplex.map (SimplexCategory.δ j.succ)
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    SimplexCategory.δ_comp_δ hij]

/-- 概要：二面から得る edgewise の重みの図式は共通の低次元の重み上で一致する。
方針：Yoneda の制限則で境界内の二面の等式へ戻す。
規約：標的 K の充填性は不要。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、面の像に運んだ図式の整合性。 -/
lemma edgewiseBoundaryFace_overlap {K : SSet.{u}} {n : ℕ}
    (a : (boundary (n + 2) : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision K)
    (i j : Fin (n + 2)) (hij : i ≤ j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ j) ≫ SSet.yonedaEquiv (boundary.ι i.castSucc ≫ a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ i) ≫ SSet.yonedaEquiv (boundary.ι j.succ ≫ a) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision_yoneda_restriction, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision_yoneda_restriction]
  congr 1
  change stdSimplex.δ j ≫ (boundary.ι i.castSucc ≫ a) =
    stdSimplex.δ i ≫ (boundary.ι j.succ ≫ a)
  rw [← Category.assoc, ← Category.assoc, boundary_faces_overlap i j hij]

/-- 概要：二つの面が同じ重みの単体を表すなら、境界から得る図式の値も一致する。
方針：pullback で共通の低次元の単体を取り、共通面上の図式の等式を評価する。
規約：任意の次数 d の共通単体を扱う。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、像の共通部分での図式の一致。 -/
lemma edgewiseBoundaryFace_eq_of_same_image {K : SSet.{u}} {n : ℕ}
    (a : (boundary (n + 2) : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision K)
    (i j : Fin (n + 2)) (hij : i ≤ j) (d : SimplexCategoryᵒᵖ)
    (x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.obj ⦋n + 1⦌).obj d)
    (hxy : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ i.castSucc)).app d x =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ j.succ)).app d y) :
    (SSet.yonedaEquiv (boundary.ι i.castSucc ≫ a)).app d x =
      (SSet.yonedaEquiv (boundary.ι j.succ ≫ a)).app d y := by
  obtain ⟨z, hzx, hzy⟩ := Types.exists_of_isPullback
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight_faces_isPullback.{u} i j hij).app d) x y hxy
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app (edgewiseBoundaryFace_overlap a i j hij) d) z
  change (SSet.yonedaEquiv (boundary.ι i.castSucc ≫ a)).app d
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ j)).app d z) =
    (SSet.yonedaEquiv (boundary.ι j.succ ≫ a)).app d
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ i)).app d z) at h
  rw [hzx, hzy] at h
  exact h

/-- 概要：順序付けた任意の異なる二面で同じ単体を表すとき図式の値は等しい。
方針：二つの添字を castSucc と succ で表示し、共通面の pullback の補題へ戻す。
規約：i<j として面を順序付ける。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、境界の面の像の共通部分での一致。 -/
lemma edgewiseBoundaryFace_eq_of_lt {K : SSet.{u}} {n : ℕ}
    (a : (boundary (n + 2) : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision K)
    (i j : Fin (n + 3)) (hij : i < j) (d : SimplexCategoryᵒᵖ)
    (x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.obj ⦋n + 1⦌).obj d)
    (hxy : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ i)).app d x =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ j)).app d y) :
    (SSet.yonedaEquiv (boundary.ι i ≫ a)).app d x =
      (SSet.yonedaEquiv (boundary.ι j ≫ a)).app d y := by
  let i' : Fin (n + 2) := ⟨i.val, by have := j.isLt; change i.val < j.val at hij; omega⟩
  let j' : Fin (n + 2) := ⟨j.val - 1, by have := j.isLt; omega⟩
  have hi : i'.castSucc = i := Fin.ext rfl
  have hj : j'.succ = j := by
    apply Fin.ext
    dsimp [j']
    change i.val < j.val at hij
    omega
  have hle : i' ≤ j' := by
    change i.val ≤ j.val - 1
    change i.val < j.val at hij
    omega
  have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ i'.castSucc)).app d x =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ j'.succ)).app d y := by
    simpa only [hi, hj] using hxy
  simpa only [hi, hj] using edgewiseBoundaryFace_eq_of_same_image a i' j' hle d x y he

/-- 概要：任意の二面で同じ重みの単体を表すなら、境界図式の値は一致する。
方針：同じ面では単射性を使い、異なる面では添字を順序付ける。
規約：全体の境界の次元は二以上。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、面の像の和上の図式を定義するための整合性。 -/
lemma edgewiseBoundaryFaces_compatible {K : SSet.{u}} {n : ℕ}
    (a : (boundary (n + 2) : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision K)
    (i j : Fin (n + 3)) (d : SimplexCategoryᵒᵖ)
    (x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.obj ⦋n + 1⦌).obj d)
    (hxy : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ i)).app d x =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ j)).app d y) :
    (SSet.yonedaEquiv (boundary.ι i ≫ a)).app d x =
      (SSet.yonedaEquiv (boundary.ι j ≫ a)).app d y := by
  rcases lt_trichotomy i j with hij | hij | hij
  · exact edgewiseBoundaryFace_eq_of_lt a i j hij d x y hxy
  · subst j
    have he : x = y := (mono_iff_injective
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.{u}.map (SimplexCategory.δ i)).app d)).mp inferInstance hxy
    subst y
    rfl
  · exact (edgewiseBoundaryFace_eq_of_lt a j i hij d y x hxy.symm).symm

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
