module

public import SerrePositivity.KST.LocalizingInvariants.InvariantLongExact
public import SerrePositivity.KST.LocalizingInvariants.NativeFiberDetection

/-!
概要：抽象 Verdier 列の端の値の整数 π 消滅から、元の像の射の同値性を得る。
方針：値の長完全列で単射・全射を示し、元の Sp の辺の整数 π 判定を使う。
規約：群の同型だけで終えず、元の関手の像の辺へ戻す。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant

variable {E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Sp.{u}} (hE : IsLocalizingInvariant E)
  (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.VerdierSequence.{u})
include hE

lemma projection_bijective_of_leftGroups
    (hA : ∀ j : ℤ, Subsingleton (valueHomotopyGroup E d.left j)) (j : ℤ) :
    Function.Bijective (valueHomotopyMap E d.projection j) := by
  constructor
  · apply (injective_iff_map_eq_one _).2
    intro a ha
    obtain ⟨b, hb⟩ := (hE.exact_middle d j a).1 ha
    rw [← hb, (hA j).elim b 1, map_one]
  · obtain ⟨k, hk⟩ : ∃ k : ℤ, k + 1 = j := ⟨j - 1, by omega⟩
    subst j
    intro a
    exact (hE.exact_right d k a).1 ((hA k).elim _ _)

lemma inclusion_bijective_of_rightGroups
    (hC : ∀ j : ℤ, Subsingleton (valueHomotopyGroup E d.right j)) (j : ℤ) :
    Function.Bijective (valueHomotopyMap E d.inclusion j) := by
  constructor
  · apply (injective_iff_map_eq_one _).2
    intro a ha
    obtain ⟨b, hb⟩ := (hE.exact_left d j a).1 ha
    rw [← hb, (hC (j + 1)).elim b 1, map_one]
  · intro a
    exact (hE.exact_middle d j a).1 ((hC j).elim _ _)

/-- 左端の全整数 π が消滅すれば、元の商関手の像は Sp の同値。 -/
lemma projection_isInvertible_of_leftGroups
    (hA : ∀ j : ℤ, Subsingleton (valueHomotopyGroup E d.left j)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow d.projection).map E).toTruncated :=
  value_isInvertible_of_piIsomorphism E d.projection
    (hE.projection_bijective_of_leftGroups d hA)

/-- 右端の全整数 π が消滅すれば、元の包含関手の像は Sp の同値。 -/
lemma inclusion_isInvertible_of_rightGroups
    (hC : ∀ j : ℤ, Subsingleton (valueHomotopyGroup E d.right j)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow d.inclusion).map E).toTruncated :=
  value_isInvertible_of_piIsomorphism E d.inclusion
    (hE.inclusion_bijective_of_rightGroups d hC)

end SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
