module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovDerivedPro

/-!
概要：有限個の層群が pro 零なら、準同型を反転する圏で元の有限切断比較は pro 同型。
方針：実隣接切断の pro 逆を整数段について反復し、元の遷移の厳密な合成式で貼る。
規約：一般 pro ∞ 圏との比較は主張しない。使われ方：LT の bounded な切断比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] (A : Tower (NonpositiveAlgebra R))

lemma postnikovTransitionLevelHom_id (n : ℤ) :
    postnikovTransitionLevelHom R A n n le_rfl = LevelHom.id (A.map (postnikovFunctor R n)) := by
  apply ProSpectrum.levelHom_ext
  intro i
  exact postnikovTransition_id R (A.obj i).obj n

lemma postnikovTransitionLevelHom_comp (a b c : ℤ) (hab : b ≤ a) (hbc : c ≤ b) :
    (postnikovTransitionLevelHom R A a b hab).comp (postnikovTransitionLevelHom R A b c hbc) =
      postnikovTransitionLevelHom R A a c (hbc.trans hab) := by
  apply ProSpectrum.levelHom_ext
  intro i
  exact postnikovTransition_comp R (A.obj i).obj a b c hab hbc

variable {C : Type v} [Category.{w} C] (L : Mon (Complex R) ⥤ C)

lemma postnikovTransitionLevelHom_isProIso_finite (hL : InvertsQuasiIsos R L)
    (b : ℤ) (hb : 0 ≤ b) (a : ℤ) (hab : b ≤ a)
    (hA : ∀ j : ℤ, b < j → j ≤ a →
      IsProZero ((A.map (nonpositiveInclusion R)).map (groups R j))) :
    IsProIso ((postnikovTransitionLevelHom R A a b hab).map L) := by
  revert hA
  induction a, hab using Int.leInduction with
  | base =>
    intro _
    rw [postnikovTransitionLevelHom_id]
    exact (IsProIso.id _).map L
  | succ a hab ih =>
    intro hA
    have ha : 0 ≤ a := hb.trans hab
    have hs := postnikovTransitionLevelHom_isProIso_succ R A L hL a ha
      (hA (a + 1) (by omega) le_rfl)
    have ht := ih (fun j hj hja => hA j hj (by omega))
    have hc := hs.comp ht
    rw [← TowerDiagram.levelHom_map_comp, postnikovTransitionLevelHom_comp] at hc
    exact hc

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
