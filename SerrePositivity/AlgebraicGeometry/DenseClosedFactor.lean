module

public import SerrePositivity.AlgebraicGeometry.SchemeImageDominance
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
概要：稠密な射上で閉部分を通る射を、全体で同じ閉部分へ因子化する。
方針：閉包含の pullback の核が零になることから同型を得る。
規約：元の対象の被約性を要求しない。
使われ方：C06 のグラフ閉包からチャート像への固有な射影。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- 稠密な射上で閉部分を通る射は、全体でその閉部分を通る。 -/
theorem exists_closed_factor_of_schemeTheoreticallyDominant
    {U Z P C : Scheme.{u}} (j : U ⟶ Z) [IsSchemeTheoreticallyDominant j]
    (p : Z ⟶ P) (c : C ⟶ P) [IsClosedImmersion c]
    (l : U ⟶ C) (h : j ≫ p = l ≫ c) :
    ∃ a : Z ⟶ C, a ≫ c = p ∧ j ≫ a = l := by
  let t : U ⟶ pullback p c := pullback.lift j l h
  let b : pullback p c ⟶ Z := pullback.fst p c
  have htb : t ≫ b = j := pullback.lift_fst _ _ _
  haveI : IsClosedImmersion b := inferInstance
  have hk : b.ker ≤ j.ker := by
    rw [← htb]
    exact Scheme.Hom.le_ker_comp t b
  haveI : IsIso b := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr
    (le_bot_iff.mp (by simpa only [j.ker_eq_bot] using hk))
  let a : Z ⟶ C := inv b ≫ pullback.snd p c
  have hac : a ≫ c = p := by
    dsimp [a]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc]
    simp [b]
  refine ⟨a, hac, ?_⟩
  apply (cancel_mono c).mp
  rw [Category.assoc, hac, h]

/-- 固有な射の、稠密な射上で決まる閉部分への因子化は固有。 -/
theorem exists_proper_closed_factor_of_schemeTheoreticallyDominant
    {U Z P C : Scheme.{u}} (j : U ⟶ Z) [IsSchemeTheoreticallyDominant j]
    (p : Z ⟶ P) [IsProper p] (c : C ⟶ P) [IsClosedImmersion c]
    (l : U ⟶ C) (h : j ≫ p = l ≫ c) :
    ∃ a : Z ⟶ C, IsProper a ∧ a ≫ c = p ∧ j ≫ a = l := by
  obtain ⟨a, hac, hja⟩ := exists_closed_factor_of_schemeTheoreticallyDominant j p c l h
  haveI : IsProper (a ≫ c) := by rw [hac]; infer_instance
  exact ⟨a, IsProper.of_comp a c, hac, hja⟩

end SerrePositivity.AlgebraicGeometry
