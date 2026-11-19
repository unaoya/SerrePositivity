module

public import SerrePositivity.CategoryTheory.Monoidal.Mod.Limits
public import SerrePositivity.Spectra.SymmetricSequence.Limits
public import SerrePositivity.Spectra.SymmetricSpectrum.Evaluation

/-! # 対称スペクトルの極限・余極限と各段の比較

内部加群の一般論を球面モノイドに適用する。
忘却関手は極限・余極限を創出し、各段の評価はこれらを保存する。
-/

@[expose] public section

universe u w w'

noncomputable section

namespace SerrePositivity.SymmetricSpectrum

open GeneralSymmetricSpectrum (level levelMap)

open CategoryTheory CategoryTheory.Limits

variable {J : Type w} [Category.{w'} J]

instance forget_createsLimits : CreatesLimitsOfSize.{w', w} (forget.{u}) :=
  inferInstanceAs (CreatesLimitsOfSize.{w', w}
    (Mod.forget (D := PointedSymmetricSequence.{u}) PointedSimplicialSet.sphereSequence.{u}))

instance forget_createsColimitsOfShape : CreatesColimitsOfShape J (forget.{u}) :=
  inferInstanceAs (CreatesColimitsOfShape J
    (Mod.forget (D := PointedSymmetricSequence.{u}) PointedSimplicialSet.sphereSequence.{u}))

instance forget_createsColimits : CreatesColimitsOfSize.{w', w} (forget.{u}) where

instance [HasLimitsOfShape J PointedSimplicialSet.{u}] :
    HasLimitsOfShape J SymmetricSpectrum.{u} :=
  inferInstanceAs (HasLimitsOfShape J
    (Mod PointedSymmetricSequence.{u} PointedSimplicialSet.sphereSequence.{u}))

instance [HasColimitsOfShape J PointedSimplicialSet.{u}] :
    HasColimitsOfShape J SymmetricSpectrum.{u} :=
  inferInstanceAs (HasColimitsOfShape J
    (Mod PointedSymmetricSequence.{u} PointedSimplicialSet.sphereSequence.{u}))

instance : HasLimitsOfSize.{u, u} SymmetricSpectrum.{u} where

instance : HasColimitsOfSize.{u, u} SymmetricSpectrum.{u} where

instance forget_preservesLimits : PreservesLimitsOfSize.{u, u} (forget.{u}) where

instance forget_preservesColimits : PreservesColimitsOfSize.{u, u} (forget.{u}) where

instance evaluation_preservesLimitsOfShape [HasLimitsOfShape J PointedSimplicialSet.{u}]
    (n : ℕ) : PreservesLimitsOfShape J (evaluation.{u} n) := by
  unfold evaluation GeneralSymmetricSpectrum.evaluation
  infer_instance

instance evaluation_preservesColimitsOfShape [HasColimitsOfShape J PointedSimplicialSet.{u}]
    (n : ℕ) : PreservesColimitsOfShape J (evaluation.{u} n) := by
  unfold evaluation GeneralSymmetricSpectrum.evaluation
  infer_instance

instance evaluation_preservesLimits (n : ℕ) :
    PreservesLimitsOfSize.{u, u} (evaluation.{u} n) where

instance evaluation_preservesColimits (n : ℕ) :
    PreservesColimitsOfSize.{u, u} (evaluation.{u} n) where

/-- 対称列を入力とする自由スペクトル関手は余極限を保存する。 -/
instance free_preservesColimits : PreservesColimitsOfSize.{w', w} (freeFunctor.{u}) :=
  (GeneralSymmetricSpectrum.freeForgetAdjunction
    PointedSimplicialSet.circle.{u}).leftAdjoint_preservesColimits

/-- 第n段を生成する自由スペクトル関手も余極限を保存する。 -/
instance freeAt_preservesColimits (n : ℕ) :
    PreservesColimitsOfSize.{w', w} (freeAt.{u} n) :=
  (freeAtAdjunction n).leftAdjoint_preservesColimits

/-- 極限スペクトルの第n段と、第n段の図式の極限との標準同型。 -/
def limitLevelIso [HasLimitsOfShape J PointedSimplicialSet.{u}]
    (F : J ⥤ SymmetricSpectrum.{u}) (n : ℕ) :
    level (limit F) n ≅ limit (F ⋙ evaluation n) := preservesLimitIso (evaluation n) F

/-- 極限の比較同型は射影と両立する。 -/
@[reassoc (attr := simp)] lemma limitLevelIso_hom_π
    [HasLimitsOfShape J PointedSimplicialSet.{u}]
    (F : J ⥤ SymmetricSpectrum.{u}) (n : ℕ) (j : J) :
    (limitLevelIso F n).hom ≫ limit.π (F ⋙ evaluation n) j = levelMap (limit.π F j) n :=
  preservesLimitIso_hom_π (evaluation n) F j

/-- 極限の逆比較も射影と両立する。 -/
@[reassoc (attr := simp)] lemma limitLevelIso_inv_π
    [HasLimitsOfShape J PointedSimplicialSet.{u}]
    (F : J ⥤ SymmetricSpectrum.{u}) (n : ℕ) (j : J) :
    (limitLevelIso F n).inv ≫ levelMap (limit.π F j) n = limit.π (F ⋙ evaluation n) j :=
  preservesLimitIso_inv_π (evaluation n) F j

/-- 余極限スペクトルの第n段と、第n段の図式の余極限との標準同型。 -/
def colimitLevelIso [HasColimitsOfShape J PointedSimplicialSet.{u}]
    (F : J ⥤ SymmetricSpectrum.{u}) (n : ℕ) :
    level (colimit F) n ≅ colimit (F ⋙ evaluation n) := preservesColimitIso (evaluation n) F

/-- 余極限の比較同型は包含と両立する。 -/
@[reassoc (attr := simp)] lemma colimitLevelIso_ι_hom
    [HasColimitsOfShape J PointedSimplicialSet.{u}]
    (F : J ⥤ SymmetricSpectrum.{u}) (n : ℕ) (j : J) :
    levelMap (colimit.ι F j) n ≫ (colimitLevelIso F n).hom = colimit.ι (F ⋙ evaluation n) j :=
  ι_preservesColimitIso_hom (evaluation n) F j

/-- 余極限の逆比較も包含と両立する。 -/
@[reassoc (attr := simp)] lemma colimitLevelIso_ι_inv
    [HasColimitsOfShape J PointedSimplicialSet.{u}]
    (F : J ⥤ SymmetricSpectrum.{u}) (n : ℕ) (j : J) :
    colimit.ι (F ⋙ evaluation n) j ≫ (colimitLevelIso F n).inv = levelMap (colimit.ι F j) n :=
  ι_preservesColimitIso_inv (evaluation n) F j

end SerrePositivity.SymmetricSpectrum
