module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.HalfRestrictions

/-!
概要：twisted arrow のホーンの各面と左右の半分の像の共通部分で図式を照合する。
方針：join の左右の包含の pullback で共通単体を取り、厳密な半分への制限則を評価する。
規約：左右の半分同士には共通単体がなく、quasicategory 性を要求しない。
使われ方：左ホーンの全ての指定データを一つの延長領域上へ接合する。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- join の左右の半分の像は、任意の次数で交わらない。 -/
lemma joinInl_app_ne_joinInr {A B : SSet.{u}} (d : SimplexCategoryᵒᵖ)
    (x : A.obj d) (y : B.obj d) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B).app d x ≠ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B).app d y := by
  obtain ⟨⟨d⟩⟩ := d
  intro he
  have hc := congrArg (fun s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B) _⦋d⦌ ↦ s.1.val) he
  change d + 1 = 0 at hc
  omega

/-- 面と右半分から同じ重みの単体を表せば、指定された図式の値も一致する。 -/
lemma twistedArrowHornFace_right_compatible {C : SSet.{u}} {n : ℕ}
    {i : Fin (n + 2)} (a : (Λ[n + 1, i] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow C)
    (b : (Δ[n + 1] : SSet.{u}) ⟶ C.op ⊗ C)
    (sq : CommSq a Λ[n + 1, i].ι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C) b)
    (j : Fin (n + 2)) (hji : j ≠ i) (d : SimplexCategoryᵒᵖ)
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.obj ⦋n⦌).obj d) (y : (Δ[n + 1] : SSet.{u}).obj d)
    (hxy : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ j)).app d x =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n + 1] : SSet.{u}).op Δ[n + 1]).app d y) :
    (SSet.yonedaEquiv (horn.ι i j hji ≫ a)).app d x = (b ≫ snd C.op C).app d y := by
  have hp := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isPullback_joinInr_naturality
    (SSet.opFunctor.map (stdSimplex.{u}.δ j)) (stdSimplex.δ j)
  obtain ⟨z, hzx, hzy⟩ := Types.exists_of_isPullback (hp.app d) x y hxy
  have h := congrArg (fun f ↦ f.app d z) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowHornFace_right_restriction a b sq j hji)
  change (SSet.yonedaEquiv (horn.ι i j hji ≫ a)).app d
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n] : SSet.{u}).op Δ[n]).app d z) =
    (b ≫ snd C.op C).app d ((stdSimplex.δ j).app d z) at h
  rw [hzx, hzy] at h
  exact h

/-- 面と左半分から同じ重みの単体を表せば、反転を戻した図式の値も一致する。 -/
lemma twistedArrowHornFace_left_compatible {C : SSet.{u}} {n : ℕ}
    {i : Fin (n + 2)} (a : (Λ[n + 1, i] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow C)
    (b : (Δ[n + 1] : SSet.{u}) ⟶ C.op ⊗ C)
    (sq : CommSq a Λ[n + 1, i].ι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C) b)
    (j : Fin (n + 2)) (hji : j ≠ i) (d : SimplexCategoryᵒᵖ)
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.obj ⦋n⦌).obj d) (y : ((Δ[n + 1] : SSet.{u}).op).obj d)
    (hxy : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ j)).app d x =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n + 1] : SSet.{u}).op Δ[n + 1]).app d y) :
    (SSet.yonedaEquiv (horn.ι i j hji ≫ a)).app d x =
      (SSet.opFunctor.map (b ≫ fst C.op C) ≫
        (SSet.opFunctorCompOpFunctorIso.app C).hom).app d y := by
  have hp := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isPullback_joinInl_naturality
    (SSet.opFunctor.map (stdSimplex.{u}.δ j)) (stdSimplex.δ j)
  obtain ⟨z, hzx, hzy⟩ := Types.exists_of_isPullback (hp.app d) x y hxy
  have h := congrArg (fun f ↦ f.app d z) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowHornFace_left_restriction a b sq j hji)
  change (SSet.yonedaEquiv (horn.ι i j hji ≫ a)).app d
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}).op Δ[n]).app d z) =
    (SSet.opFunctor.map (b ≫ fst C.op C) ≫
      (SSet.opFunctorCompOpFunctorIso.app C).hom).app d
      ((SSet.opFunctor.map (stdSimplex.δ j)).app d z) at h
  rw [hzx, hzy] at h
  exact h

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
