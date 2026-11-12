module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovOneConnectivePro
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraInvariantQuasiIso
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraInvariantTowers

/-!
概要：元の π₀・π₁ 群の pro 同型を、元の一切断の実不変量値の pro 同型へ送る。
方針：具体的 IsKConnective の connective 準同型反転を、元の class 模型の逆へ使う。
規約：任意の高次有限段や LT 全体とは主張しない。使われ方：実値の塔の有限比較。
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

def postnikovOneValueMap := invariantLevelMap R Φ (f.map (postnikovFunctor R 1))

lemma IsKConnective.postnikovOneValueMap_isProIso {k : ℤ} (h : IsKConnective R Φ k)
    (h₀ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0)))
    (h₁ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 1))) :
    IsProIso (postnikovOneValueMap R Φ f) :=
  postnikovOneMap_isProIso_of_connective R f (invariantFunctor R Φ)
    (h.invariantFunctor_invertsConnectiveQuasiIsos R Φ) h₀ h₁

lemma IsKConnective.postnikovOneValueMap_piProEquivalence {k : ℤ} (h : IsKConnective R Φ k)
    (h₀ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0)))
    (h₁ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 1))) :
    ProSpectrum.IsPiProEquivalence (postnikovOneValueMap R Φ f) :=
  ProSpectrum.piProEquivalence_of_proIso (h.postnikovOneValueMap_isProIso R Φ f h₀ h₁)

lemma IsKConnective.nonpositiveMap_value_isProIso_of_oneBounded
    {k : ℤ} (h : IsKConnective R Φ k)
    (hA : ∀ i, (A.obj i).obj.X.IsGE (-1)) (hB : ∀ i, (B.obj i).obj.X.IsGE (-1))
    (h₀ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0)))
    (h₁ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 1))) :
    IsProIso (invariantLevelMap R Φ (f.map (nonpositiveInclusion R))) :=
  nonpositiveMap_isProIso_of_oneBounded_connective R f (invariantFunctor R Φ)
    (h.invariantFunctor_invertsConnectiveQuasiIsos R Φ) hA hB h₀ h₁

lemma IsKConnective.nonpositiveMap_value_piProEquivalence_of_oneBounded
    {k : ℤ} (h : IsKConnective R Φ k)
    (hA : ∀ i, (A.obj i).obj.X.IsGE (-1)) (hB : ∀ i, (B.obj i).obj.X.IsGE (-1))
    (h₀ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0)))
    (h₁ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 1))) :
    ProSpectrum.IsPiProEquivalence (invariantLevelMap R Φ (f.map (nonpositiveInclusion R))) :=
  ProSpectrum.piProEquivalence_of_proIso
    (h.nonpositiveMap_value_isProIso_of_oneBounded R Φ f hA hB h₀ h₁)

lemma IsKConnective.postnikovOneValueMap_piProEquivalence_of_proConnected
    {k : ℤ} (h : IsKConnective R Φ k)
    (hf : IsPiProConnected R (f.map (nonpositiveInclusion R)) 2) :
    ProSpectrum.IsPiProEquivalence (postnikovOneValueMap R Φ f) :=
  h.postnikovOneValueMap_piProEquivalence R Φ f
    (hf.groupMap_isProIso R (by omega)) (hf.groupMap_isProIso R (by omega))

lemma IsKConnective.nonpositiveMap_value_piProEquivalence_of_oneBounded_proConnected
    {k : ℤ} (h : IsKConnective R Φ k)
    (hA : ∀ i, (A.obj i).obj.X.IsGE (-1)) (hB : ∀ i, (B.obj i).obj.X.IsGE (-1))
    (hf : IsPiProConnected R (f.map (nonpositiveInclusion R)) 2) :
    ProSpectrum.IsPiProEquivalence (invariantLevelMap R Φ (f.map (nonpositiveInclusion R))) :=
  h.nonpositiveMap_value_piProEquivalence_of_oneBounded R Φ f hA hB
    (hf.groupMap_isProIso R (by omega)) (hf.groupMap_isProIso R (by omega))

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
