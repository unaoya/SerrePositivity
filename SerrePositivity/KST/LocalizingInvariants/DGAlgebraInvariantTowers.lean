module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraInvariantFunctor
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraInvariantConnectivity
public import SerrePositivity.KST.LocalizingInvariants.SpectrumPiNativeConnectivity
public import SerrePositivity.KST.LocalizingInvariants.ProSpectrumEventualConnectivity

/-!
概要：元の dg 代数の塔とレベル射から実値の塔を構成し、共終な連結度を π-pro 同値へ送る。
方針：元の値の実関手で遷移と自然性を写し、具体的 k-connective 条件を適用する。
規約：値の塔やその関手則を入力しない。使われ方：LT Cor. 2.31 の実値の判定段階。
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

def invariantTower (A : Tower (Mon (Complex R))) : ProSpectrum.Tower.{u + 1} :=
  A.map (invariantFunctor R Φ)

def invariantLevelMap {A B : Tower (Mon (Complex R))} (f : LevelHom A B) :
    ProSpectrum.LevelHom (invariantTower R Φ A) (invariantTower R Φ B) :=
  f.map (invariantFunctor R Φ)

variable {k : ℤ} (h : IsKConnective R Φ k) {A B : Tower (Mon (Complex R))}
  (f : LevelHom A B) (hA : ∀ i, IsConnective R (A.obj i))
  (hB : ∀ i, IsConnective R (B.obj i))

include h hA hB in
lemma IsKConnective.invariantLevelMap_cofinal_piProEquivalence
    (hc : ∀ n : ℤ, 1 ≤ n → ∀ i, ∃ s, ∃ _hi : i ≤ s, IsConnected R (f.app s) n) :
    ProSpectrum.IsPiProEquivalence (invariantLevelMap R Φ f) := by
  apply ProSpectrum.piProEquivalence_of_cofinal_connected
  intro n i
  let d : ℤ := max 1 (n - k)
  have hd : 1 ≤ d := le_max_left _ _
  obtain ⟨s, hi, hs⟩ := hc d hd i
  have hz : Function.Bijective ((groups R 0).map (f.app s)).hom :=
    ⟨hs.1 0 (by omega), hs.2 0 (by omega)⟩
  have hv := h.2 (hA s) (hB s) (f.app s) d hd hz hs
  refine ⟨s, hi, SpectrumHo.isPiConnected_of_native (invariantMap R Φ (f.app s)) n ?_ ?_⟩
  · intro j hj
    exact hv.1 j (by dsimp [d] at *; omega)
  · intro j hj
    exact hv.2 j (by dsimp [d] at *; omega)

include h hA hB in
lemma IsKConnective.invariantLevelMap_eventual_piProEquivalence
    (hc : ∀ n : ℤ, 1 ≤ n → ∃ t, ∀ s, t ≤ s → IsConnected R (f.app s) n) :
    ProSpectrum.IsPiProEquivalence (invariantLevelMap R Φ f) := by
  apply IsKConnective.invariantLevelMap_cofinal_piProEquivalence R Φ h f hA hB
  intro n hn i
  obtain ⟨t, ht⟩ := hc n hn
  exact ⟨max i t, le_max_left _ _, ht _ (le_max_right _ _)⟩

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
