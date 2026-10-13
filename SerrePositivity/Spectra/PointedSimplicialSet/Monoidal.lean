module

public import SerrePositivity.Spectra.PointedSimplicialSet.InternalHom
public import SerrePositivity.Spectra.Pointed.SmashMonoidal

/-!
# 基点付き単体的集合の閉対称モノイダル構造

SSet の閉直積構造・等化子・有限余極限から、通常の smash の構造を得る。
Mathlib のテンソル積・内部 Hom・評価が、構成済みの具体的な対象・射と一致する。
対称列やスペクトルに使う基礎圏の入口であり、モデル構造はまだ含まない。
-/

@[expose] public section

universe u

noncomputable section

namespace SerrePositivity.PointedSimplicialSet

open CategoryTheory CategoryTheory.MonoidalCategory

example : MonoidalCategory PointedSimplicialSet.{u} := inferInstance
example : SymmetricCategory PointedSimplicialSet.{u} := inferInstance
example : MonoidalClosed PointedSimplicialSet.{u} := inferInstance

/-- モノイダル積は通常の smash。 -/
lemma tensorObj_eq_smash (X Y : PointedSimplicialSet.{u}) :
    X ⊗ Y = PointedObject.smash X Y := rfl

/-- 単位対象は自由な基点を付けた零次球面。 -/
lemma tensorUnit_eq_sphereZero : 𝟙_ PointedSimplicialSet.{u} = sphereZero := rfl

/-- Mathlib の内部 Hom は既存の基点付き内部 Hom と同じ。 -/
lemma ihom_obj_eq_internalHom (X Y : PointedSimplicialSet.{u}) :
    (ihom X).obj Y = internalHom X Y := rfl

/-- Mathlib の評価射は smash の随伴から構成した評価射と同じ。 -/
lemma ihom_ev_app_eq_smashEvaluation (X Y : PointedSimplicialSet.{u}) :
    (ihom.ev X).app Y = PointedObject.smashEvaluation X Y := rfl

end SerrePositivity.PointedSimplicialSet
