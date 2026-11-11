module

public import SerrePositivity.KST.LocalizingInvariants.LocalizationHomotopyCategory
public import SerrePositivity.KST.LocalizingInvariants.TammeFiniteDenominators

/-!
概要：一般 Tamme 商の h 圏は通常局所化であり、実辺は元の分母による二単体を持つ。
方針：全関手 ∞ 圏の普遍性を h へ下ろし、右分数を元の頂点・辺・合成二単体に戻す。
規約：商内の入力辺を固定する。使われ方：矢印図式の商への移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {C D E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)

instance tammeQuotientHo_isLocalization :
    (hoFunctor.map (tammeQuotientMap p q)).toFunctor.IsLocalization
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage (pullbackInclusion p q))).trW :=
  localizationHo_isLocalization _ _ (tammeQuotient_isLocalization p q) _
    (fun e => (tammeLocalizingEdges_iff_trW p q e).symm)

/-- 商の実辺は、元の実分母で前合成すると元の実辺の像となる。 -/
lemma tammeQuotient_edge_fraction {x y : (laxCategory p q).obj _⦋0⦌}
    (f : Truncated.Edge (X := (truncation 2).obj (tammeQuotient p q))
      ((tammeQuotientMap p q).app (Opposite.op ⦋0⦌) x)
      ((tammeQuotientMap p q).app (Opposite.op ⦋0⦌) y)) :
    ∃ (a : (laxCategory p q).obj _⦋0⦌)
      (s : Truncated.Edge (X := (truncation 2).obj (laxCategory p q).obj) a x)
      (g : Truncated.Edge (X := (truncation 2).obj (laxCategory p q).obj) a y),
      s.edge ∈ tammeLocalizingEdges p q ∧
      Nonempty (Truncated.Edge.CompStruct
        (s.map ((truncation 2).map (tammeQuotientMap p q))) f
        (g.map ((truncation 2).map (tammeQuotientMap p q)))) := by
  let L := (hoFunctor.map (tammeQuotientMap p q)).toFunctor
  let V := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage (pullbackInclusion p q))).trW
  obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction L V
    (X := HomotopyCategory.mk x) (Y := HomotopyCategory.mk y)
    (SSet.Truncated.HomotopyCategory.homMk f)
  have h := φ.map_s_comp_map L (Localization.inverts L V)
  rw [← hφ] at h
  rcases φ with @⟨a, s, hs, g⟩
  obtain ⟨a, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective a
  obtain ⟨s, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective a x s
  obtain ⟨g, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective a y g
  exact ⟨a, s, g, (tammeLocalizingEdges_iff_trW p q s).mpr hs,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac h⟩

end SerrePositivity.KST.LocalizingInvariants
