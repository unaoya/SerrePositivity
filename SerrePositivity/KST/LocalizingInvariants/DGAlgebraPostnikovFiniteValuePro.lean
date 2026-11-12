module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraInvariantQuasiIso
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraInvariantTowers
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovBoundedDerivedPro

/-!
概要：有限範囲の層群の pro 零性から、元の実 Postnikov 値の塔の pro 同型を構成する。
方針：connective 準同型の反転と乗法的経路の値の等式を、実 roof の pro 逆へ送る。
規約：元の値の塔と元の切断比較を保持。使われ方：LT の有限切断と値の塔の接続。
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
  (A : Tower (NonpositiveAlgebra R))

def postnikovValueTransition (a b : ℤ) (hab : b ≤ a) :
    ProSpectrum.LevelHom (invariantTower R Φ (A.map (postnikovFunctor R a)))
      (invariantTower R Φ (A.map (postnikovFunctor R b))) :=
  invariantLevelMap R Φ (postnikovTransitionLevelHom R A a b hab)

def postnikovValueQuotient (b : ℤ) :
    ProSpectrum.LevelHom (invariantTower R Φ (A.map (nonpositiveInclusion R)))
      (invariantTower R Φ (A.map (postnikovFunctor R b))) :=
  invariantLevelMap R Φ (postnikovQuotientLevelHom R A b)

lemma IsKConnective.postnikovValueTransition_isProIso_finite
    {k : ℤ} (h : IsKConnective R Φ k) (b : ℤ) (hb : 0 ≤ b) (a : ℤ) (hab : b ≤ a)
    (hA : ∀ j : ℤ, b < j → j ≤ a →
      IsProZero ((A.map (nonpositiveInclusion R)).map (groups R j))) :
    IsProIso (postnikovValueTransition R Φ A a b hab) :=
  postnikovTransitionLevelHom_isProIso_finite_of_connective R A (invariantFunctor R Φ)
    (h.invariantFunctor_invertsConnectiveQuasiIsos R Φ) b hb a hab hA

lemma IsKConnective.postnikovValueQuotient_isProIso_of_bounded
    {k : ℤ} (h : IsKConnective R Φ k) (b : ℤ) (hb : 0 ≤ b) (a : ℤ) (hab : b ≤ a)
    (hB : ∀ i, (A.obj i).obj.X.IsGE (-a))
    (hA : ∀ j : ℤ, b < j → j ≤ a →
      IsProZero ((A.map (nonpositiveInclusion R)).map (groups R j))) :
    IsProIso (postnikovValueQuotient R Φ A b) :=
  postnikovQuotientLevelHom_isProIso_of_bounded_connective R A (invariantFunctor R Φ)
    (h.invariantFunctor_invertsConnectiveQuasiIsos R Φ) b hb a hab hB hA

lemma IsKConnective.postnikovValueTransition_piProEquivalence
    {k : ℤ} (h : IsKConnective R Φ k) (b : ℤ) (hb : 0 ≤ b) (a : ℤ) (hab : b ≤ a)
    (hA : ∀ j : ℤ, b < j → j ≤ a →
      IsProZero ((A.map (nonpositiveInclusion R)).map (groups R j))) :
    ProSpectrum.IsPiProEquivalence (postnikovValueTransition R Φ A a b hab) :=
  ProSpectrum.piProEquivalence_of_proIso
    (h.postnikovValueTransition_isProIso_finite R Φ A b hb a hab hA)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
