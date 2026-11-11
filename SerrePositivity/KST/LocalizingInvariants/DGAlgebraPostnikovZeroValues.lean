module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovZeroPro
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraInvariantTowers

/-!
概要：元の π₀ 群の pro 同型を、元の零切断代数の不変量値の実 pro 同型へ送る。
方針：単位・積を保つ元の零切断の pro 逆を、構成済みの元の実値関手で写す。
規約：値の連結度条件を追加しない。使われ方：LT の有限切断比較の零段。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] (Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} ⟶ Sp.{u + 1})
  {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)

lemma postnikovZeroValueMap_isProIso
    (hf : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0))) :
    IsProIso (invariantLevelMap R Φ (f.map (postnikovFunctor R 0))) :=
  (postnikovZeroMap_isProIso R f hf).map (invariantFunctor R Φ)

lemma postnikovZeroValueMap_piProEquivalence
    (hf : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0))) :
    ProSpectrum.IsPiProEquivalence (invariantLevelMap R Φ (f.map (postnikovFunctor R 0))) :=
  ProSpectrum.piProEquivalence_of_proIso (postnikovZeroValueMap_isProIso R Φ f hf)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
