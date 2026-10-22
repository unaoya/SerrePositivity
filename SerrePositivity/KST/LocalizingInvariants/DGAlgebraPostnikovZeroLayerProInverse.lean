module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovZeroLayerFunctor
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovZeroPro
public import SerrePositivity.KST.LocalizingInvariants.ProInverseAfter

/-!
概要：元の π₀・πₙ₊₁ 群の pro 同型から、零底と層の平方零代数の実 pro 逆を構成。
方針：元の直和二成分の pro 逆を作り、既存の二段補正で単位・積保存を回収する。
規約：双加群逆を入力しない。使われ方：係数逆の作用保存と細分 roof の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] (n : ℤ)
  {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  (h₀ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0)))
  (hₙ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R (n + 1))))

include h₀ hₙ in
lemma postnikovZeroLayerAlgebraMap_isProIso :
    IsProIso (f.map (postnikovZeroLayerAlgebraFunctor R n)) := by
  have hb := (postnikovZeroMap_isProIso R f h₀).map (Mon.forget (Complex R))
  have hl := postnikovLayerMap_isProIso R n f hₙ
  have hp := (TowerDiagram.proIso_prod'
    (F := postnikovFunctor R 0 ⋙ Mon.forget (Complex R))
    (G := postnikovLayerFunctor R n) f hb hl).map (cochainBiproductFunctor R)
  have hc := TowerDiagram.proIso_of_natIso (postnikovZeroLayerAlgebraComplexIso R n) f hp
  exact TowerDiagram.proIso_of_monoid_forget _ hc

include h₀ hₙ in
lemma exists_postnikovZeroLayerAlgebraInverse_after (i bound : ℕ) :
    ∃ k, ∃ hi : i ≤ k, bound ≤ k ∧
      ∃ r : postnikovZeroLayerAlgebra R (B.obj k).obj n ⟶
        postnikovZeroLayerAlgebra R (A.obj i).obj n,
      postnikovZeroLayerAlgebraMap R n (f.app k).hom ≫ r =
        postnikovZeroLayerAlgebraMap R n (A.transition hi).hom ∧
      r ≫ postnikovZeroLayerAlgebraMap R n (f.app i).hom =
        postnikovZeroLayerAlgebraMap R n (B.transition hi).hom :=
  TowerDiagram.exists_inverse_after _ (postnikovZeroLayerAlgebraMap_isProIso R n f h₀ hₙ)
    i bound

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
