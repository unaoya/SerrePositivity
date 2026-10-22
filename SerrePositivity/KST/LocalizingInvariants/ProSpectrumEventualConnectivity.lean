module

public import SerrePositivity.KST.LocalizingInvariants.SpectrumPiConnectivity
public import SerrePositivity.KST.LocalizingInvariants.ProSpectrumIsoCriterion

/-!
概要：値の塔のレベル射が任意の連結度を共終な段で満たせば、元の射は π-pro 同値。
方針：各整数次数と各始点の先で全単射となる段を選び、実遷移で核と像を比較する。
規約：一般 pro ∞ 圏での同値とは主張しない。使われ方：LT の値の塔の連結度判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
namespace SerrePositivity.KST.LocalizingInvariants
open ProExcision

namespace ProGroup
lemma proIso_of_cofinal_bijective {X Y : Tower CommGrpCat.{u}} (f : LevelHom X Y)
    (h : ∀ m, ∃ s, ∃ hm : m ≤ s, Function.Bijective (f.app s).hom) : IsProIso f := by
  apply proIso_of_kernel_image
  · intro m
    obtain ⟨s, hm, hs⟩ := h m
    refine ⟨s, hm, fun x hx => ?_⟩
    have he : x = 1 := hs.1 (hx.trans (map_one _).symm)
    rw [he, map_one]
  · intro m
    obtain ⟨s, hm, hs⟩ := h m
    refine ⟨s, hm, fun y => ?_⟩
    obtain ⟨x, hx⟩ := hs.2 y
    refine ⟨(X.transition hm).hom x, ?_⟩
    have he := congrArg (fun t => t.hom x) (f.naturality hm)
    change (f.app m).hom ((X.transition hm).hom x) =
      (Y.transition hm).hom ((f.app s).hom x) at he
    exact he.trans (congrArg (Y.transition hm).hom hx)
end ProGroup

namespace ProSpectrum
lemma piProEquivalence_of_cofinal_bijective {X Y : Tower.{u}} (f : LevelHom X Y)
    (h : ∀ j : ℤ, ∀ m, ∃ s, ∃ hm : m ≤ s,
      Function.Bijective ((SpectrumHo.piFunctor j).map (f.app s)).hom) :
    IsPiProEquivalence f := by
  intro j
  exact ProGroup.proIso_of_cofinal_bijective (f.map (SpectrumHo.piFunctor j)) (h j)

lemma piProEquivalence_of_cofinal_connected {X Y : Tower.{u}} (f : LevelHom X Y)
    (h : ∀ n : ℤ, ∀ m, ∃ s, ∃ hm : m ≤ s, SpectrumHo.IsPiConnected (f.app s) n) :
    IsPiProEquivalence f := by
  apply piProEquivalence_of_cofinal_bijective f
  intro j m
  obtain ⟨s, hm, hs⟩ := h (j + 1) m
  exact ⟨s, hm, hs.1 j (by omega), hs.2 j (by omega)⟩
lemma piProEquivalence_of_eventually_connected {X Y : Tower.{u}} (f : LevelHom X Y)
    (h : ∀ n : ℤ, ∃ t, ∀ s, t ≤ s → SpectrumHo.IsPiConnected (f.app s) n) :
    IsPiProEquivalence f := by
  apply piProEquivalence_of_cofinal_connected f
  intro n m
  obtain ⟨t, ht⟩ := h n
  exact ⟨max m t, le_max_left _ _, ht _ (le_max_right _ _)⟩

end ProSpectrum
end SerrePositivity.KST.LocalizingInvariants
