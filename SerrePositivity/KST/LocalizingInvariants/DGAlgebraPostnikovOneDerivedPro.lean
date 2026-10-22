module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovClassProReflection
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraQuasiIsoLocalization

/-!
概要：元の π₀・π₁ 群の pro 同型から、元の一切断射の局所化後の実 pro 逆を構成する。
方針：零底を揃えた class 模型の逆を元の源射へ戻し、元の右射影の実逆を合成する。
規約：高次有限段・一般 pro ∞ 同値は未主張。使われ方：LT の有限 Postnikov 比較。
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
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {D : Type v} [Category.{w} D] (L : Mon (Complex R) ⥤ D)

lemma postnikovNormalizedSource_isProIso_of_inverts (hL : InvertsQuasiIsos R L)
    (hf : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 1))) :
    IsProIso ((postnikovStrictZeroBaseLift R f 1 (by omega)).map L) := by
  let a := postnikovStrictZeroBaseNonpositiveLift R f 1 (by omega)
  have hc := postnikovClassModelMap_reflects_proIso R a L hL 0 (by omega)
    (postnikovNormalizedClassModelMap_isProIso R f L hL hf)
  apply postnikovMap_reflects_proIso_of_bounded R a L hL 1 ?_ ?_ hc
  · intro i
    change (postnikov R (A.obj i).obj 1).X.IsGE (-1)
    have : (postnikov R (A.obj i).obj 1).X.IsStrictlyGE (-1) :=
      postnikovComplex_lowerBound R (A.obj i).obj 1
    infer_instance
  · intro i
    change ((postnikovStrictZeroBaseTower R f 1 (by omega)).obj i).X.IsGE (-1)
    have := postnikovStrictZeroBase_lowerBound R f 1 (by omega) i
    infer_instance

lemma postnikovOneMap_isProIso_of_inverts (hL : InvertsQuasiIsos R L)
    (h₀ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0)))
    (h₁ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 1))) :
    IsProIso ((f.map (postnikovFunctor R 1)).map L) := by
  have ha := postnikovNormalizedSource_isProIso_of_inverts R f L hL h₁
  have hb := (postnikovStrictZeroBaseProjection_isProIso R f 1 (by omega) h₀).map L
  have hc := ha.comp hb
  rw [← TowerDiagram.levelHom_map_comp, postnikovStrictZeroBase_fac] at hc
  exact hc

lemma postnikovOneMap_localized_isProIso
    (h₀ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0)))
    (h₁ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 1))) :
    IsProIso ((f.map (postnikovFunctor R 1)).map (quasiIsoLocalization R)) :=
  postnikovOneMap_isProIso_of_inverts R f (quasiIsoLocalization R)
    (quasiIsoLocalization_inverts R) h₀ h₁

lemma nonpositiveMap_localized_isProIso_of_oneBounded
    (hA : ∀ i, (A.obj i).obj.X.IsGE (-1)) (hB : ∀ i, (B.obj i).obj.X.IsGE (-1))
    (h₀ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0)))
    (h₁ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 1))) :
    IsProIso ((f.map (nonpositiveInclusion R)).map (quasiIsoLocalization R)) :=
  postnikovMap_reflects_proIso_of_bounded R f (quasiIsoLocalization R)
    (quasiIsoLocalization_inverts R) 1 hA hB (postnikovOneMap_localized_isProIso R f h₀ h₁)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
