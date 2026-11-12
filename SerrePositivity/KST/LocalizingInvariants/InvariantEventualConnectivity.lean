module

public import SerrePositivity.KST.LocalizingInvariants.InvariantConnectivity
public import SerrePositivity.KST.LocalizingInvariants.ProSpectrumEventualConnectivity

/-!
概要：元の塔の共終なレベル連結度から、k-connective 不変量の値の π-pro 同値を得る。
方針：各必要次数に応じた連結度を選び、同じ実レベル射への連結度条件を適用する。
規約：値の塔の実関手とレベル表示は明示的入力。使われ方：LT Cor. 2.31 の値の判定。
-/

@[expose] public section
noncomputable section
universe u v w
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants
variable {C : Type v} [Category.{w} C]
  {Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Sp.{u}} {U : C ⥤ hoFunctor.obj Sp.{u}}
  {P : C ⥤ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {k : ℤ}

lemma IsKConnectiveOn.cofinal_levelMap_piProEquivalence
    (h : IsKConnectiveOn Φ U P k) {X Y : ProExcision.Tower C}
    (f : ProExcision.LevelHom X Y)
    (hc : ∀ n : ℤ, ∀ m, ∃ s, ∃ hm : m ≤ s, SpectrumHo.IsPiConnected (U.map (f.app s)) n) :
    ProSpectrum.IsPiProEquivalence (f.map (P ⋙ stableValueFunctor Φ)) := by
  apply ProSpectrum.piProEquivalence_of_cofinal_connected
  intro n m
  let r : ℤ := max 1 (n - k)
  have hr : 1 ≤ r := le_max_left _ _
  have hn : n ≤ r + k := by have ht := le_max_right 1 (n - k); omega
  obtain ⟨s, hm, hs⟩ := hc r m
  have hv := h.2.2 (f.app s) r hr (hs.piZeroIso hr) hs
  exact ⟨s, hm, (fun j hj => hv.1 j (by omega)), fun j hj => hv.2 j (by omega)⟩

end SerrePositivity.KST.LocalizingInvariants
