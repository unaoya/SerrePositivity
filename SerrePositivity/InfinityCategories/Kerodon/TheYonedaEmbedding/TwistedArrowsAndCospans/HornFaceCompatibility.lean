module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.HornLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseFacePullbacks

/-!
概要：twisted arrow のホーンの二つの面の重みの共通部分で、指定された図式は一致する。
方針：共通部分の pullback で一つ低い重みへ戻し、ホーンの単射性と Yoneda の自然性を使う。
規約：ホーンの欠ける面を含めず、一次元も同じ面の単射性で扱う。
使われ方：左右の半分とホーンの各面の像の和への図式の接合。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 異なる二面を順序付けると、ホーン上の図式は重みの共通部分で一致する。 -/
lemma edgewiseHornFaces_compatible_of_lt {C : SSet.{u}} {n : ℕ}
    {k : Fin (n + 3)} (a : (Λ[n + 2, k] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow C)
    (i j : Fin (n + 3)) (hik : i ≠ k) (hjk : j ≠ k) (hij : i < j)
    (d : SimplexCategoryᵒᵖ) (x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.obj ⦋n + 1⦌).obj d)
    (hxy : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ i)).app d x =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ j)).app d y) :
    (SSet.yonedaEquiv (horn.ι k i hik ≫ a)).app d x =
      (SSet.yonedaEquiv (horn.ι k j hjk ≫ a)).app d y := by
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
  obtain ⟨z, hzx, hzy⟩ := Types.exists_of_isPullback
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight_faces_isPullback.{u} i' j' hle).app d) x y he
  have hover : stdSimplex.δ j' ≫ horn.ι k i hik =
      stdSimplex.δ i' ≫ horn.ι k j hjk := by
    apply (cancel_mono (horn.{u} (n + 2) k).ι).mp
    simp only [Category.assoc, horn.ι_ι]
    rw [← hi, ← hj]
    change stdSimplex.map (SimplexCategory.δ j') ≫ stdSimplex.map _ =
      stdSimplex.map (SimplexCategory.δ i') ≫ stdSimplex.map _
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      SimplexCategory.δ_comp_δ hle]
  have hw : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ j') ≫
      SSet.yonedaEquiv (horn.ι k i hik ≫ a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ i') ≫
        SSet.yonedaEquiv (horn.ι k j hjk ≫ a) := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision_yoneda_restriction, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision_yoneda_restriction]
    congr 1
    change stdSimplex.δ j' ≫ (horn.ι k i hik ≫ a) =
      stdSimplex.δ i' ≫ (horn.ι k j hjk ≫ a)
    rw [← Category.assoc, ← Category.assoc, hover]
  have h := congrArg (fun f ↦ f.app d z) hw
  change (SSet.yonedaEquiv (horn.ι k i hik ≫ a)).app d
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ j')).app d z) =
    (SSet.yonedaEquiv (horn.ι k j hjk ≫ a)).app d
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ i')).app d z) at h
  rw [hzx, hzy] at h
  exact h

/-- ホーンの任意の二面の像上で、元の図式の値は一致する。 -/
lemma edgewiseHornFaces_compatible {C : SSet.{u}} {n : ℕ}
    {k : Fin (n + 2)} (a : (Λ[n + 1, k] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow C)
    (i j : Fin (n + 2)) (hik : i ≠ k) (hjk : j ≠ k)
    (d : SimplexCategoryᵒᵖ) (x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.obj ⦋n⦌).obj d)
    (hxy : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ i)).app d x =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ j)).app d y) :
    (SSet.yonedaEquiv (horn.ι k i hik ≫ a)).app d x =
      (SSet.yonedaEquiv (horn.ι k j hjk ≫ a)).app d y := by
  by_cases heq : i = j
  · subst j
    have he : x = y := (mono_iff_injective
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.{u}.map (SimplexCategory.δ i)).app d)).mp inferInstance hxy
    subst y
    rfl
  · cases n with
    | zero =>
      have hi := i.isLt
      have hj := j.isLt
      have hk := k.isLt
      have h1 : i.val ≠ k.val := fun h ↦ hik (Fin.ext h)
      have h2 : j.val ≠ k.val := fun h ↦ hjk (Fin.ext h)
      exact False.elim (heq (Fin.ext (by omega)))
    | succ n =>
      rcases lt_or_gt_of_ne heq with hij | hij
      · exact edgewiseHornFaces_compatible_of_lt a i j hik hjk hij d x y hxy
      · exact (edgewiseHornFaces_compatible_of_lt a j i hjk hik hij d y x hxy.symm).symm

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
