module

public import SerrePositivity.InfinityCategories.F2.Ind.IntervalSliceConeBoundary
public import SerrePositivity.InfinityCategories.F2.Ind.IntervalTerminalSliceSection
public import SerrePositivity.InfinityCategories.F2.Ind.RightFibrationPrismCorner

/-!
概要：元の全円柱を、始点の全錐と元の終端辺を保って終点 slice へ持ち上げる。
方針：区間の全錐の組み替えと標準終点切断の始点を照合し、right fibration で延長。
規約：元の全底図式を厳密に回収。使われ方：終点 comma の円柱族 F の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 指定した元の全錐を始点とし、終端側面を元の辺とする全円柱の slice 持ち上げ。 -/
lemma exists_intervalSlice_prism_lift {A X : SSet.{u}} [Quasicategory X]
    (d : (Δ[1] : SSet.{u}) ⟶ X) (f : A ⟶ sliceOver d)
    (b : join A (Δ[0] : SSet.{u}) ⊗ Δ[1] ⟶ X)
    (h₀ : (join A (Δ[0] : SSet.{u}) ◁ stdSimplex.δ 1) ≫ b =
      fst (join A Δ[0]) Δ[0] ≫ sliceOverUncurry (f ≫ sliceOverRestrict d (stdSimplex.δ 1)))
    (ht : (joinInr A (Δ[0] : SSet.{u}) ▷ Δ[1]) ≫ b = snd Δ[0] Δ[1] ≫ d) :
    ∃ W : join A (Δ[0] : SSet.{u}) ⊗ Δ[1] ⟶ sliceOver (stdSimplex.δ 0 ≫ d),
      W ≫ sliceOverProjection (stdSimplex.δ 0 ≫ d) = b ∧
      (join A (Δ[0] : SSet.{u}) ◁ stdSimplex.δ 1) ≫ W =
        fst (join A Δ[0]) Δ[0] ≫ intervalSliceConeLift d f ∧
      (joinInr A (Δ[0] : SSet.{u}) ▷ Δ[1]) ≫ W =
        snd Δ[0] Δ[1] ≫ intervalTerminalSliceSection d := by
  have hc : joinInr A (Δ[0] : SSet.{u}) ≫ intervalSliceConeLift d f =
      stdSimplex.δ 1 ≫ intervalTerminalSliceSection d := by
    apply sliceOverUncurry_injective
    rw [intervalSliceConeLift_tip, intervalTerminalSliceSection_first]
  have h : (joinInr A (Δ[0] : SSet.{u}) ▷ Δ[0]) ≫
      (fst (join A Δ[0]) Δ[0] ≫ intervalSliceConeLift d f) =
        (Δ[0] ◁ stdSimplex.δ 1) ≫ (snd Δ[0] Δ[1] ≫ intervalTerminalSliceSection d) := by
    rw [← Category.assoc, whiskerRight_fst, Category.assoc, hc,
      ← Category.assoc (Δ[0] ◁ stdSimplex.δ 1), whiskerLeft_snd]
    rw [show fst (Δ[0] : SSet.{u}) Δ[0] = snd Δ[0] Δ[0] from
      stdSimplex.isTerminalObj₀.hom_ext _ _]
    rw [Category.assoc]
  have ha : (fst (join A (Δ[0] : SSet.{u})) Δ[0] ≫ intervalSliceConeLift d f) ≫
      sliceOverProjection (stdSimplex.δ 0 ≫ d) =
        (join A (Δ[0] : SSet.{u}) ◁ stdSimplex.δ 1) ≫ b := by
    rw [Category.assoc, intervalSliceConeLift_projection]
    exact h₀.symm
  have hd : (snd (Δ[0] : SSet.{u}) Δ[1] ≫ intervalTerminalSliceSection d) ≫
      sliceOverProjection (stdSimplex.δ 0 ≫ d) = (joinInr A Δ[0] ▷ Δ[1]) ≫ b := by
    rw [Category.assoc, intervalTerminalSliceSection_projection]
    exact ht.symm
  have he : scaffoldFirstVertex 1 = (stdSimplex.δ 1 : (Δ[0] : SSet.{u}) ⟶ Δ[1]) := by
    rw [scaffoldFirstVertex, stdSimplex.δ_one_eq_const, SSet.yonedaEquiv_symm_zero]
  obtain ⟨W, hp, hW, htW⟩ := exists_rightFibration_prism_corner_lift
    (sliceOverProjection (stdSimplex.δ 0 ≫ d)) (joinInr A Δ[0]) (conePoint_rightAnodyne A)
    b (fst (join A Δ[0]) Δ[0] ≫ intervalSliceConeLift d f)
    (snd Δ[0] Δ[1] ≫ intervalTerminalSliceSection d) (by simpa only [he] using h)
    (by simpa only [he] using ha) hd
  exact ⟨W, hp, by simpa only [he] using hW, htW⟩

end SerrePositivity.InfinityCategories.F2.Ind
