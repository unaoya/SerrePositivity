module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.IdentityCommaCollapsedCoefficients
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.IdentityCommaTerminalMain
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CommaPrismPhaseCongruence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CommaTerminalCut
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.SimplexCoefficientExt

/-! 恒等 augmentation 終端への切断後、相 β と β ⊔ t は全単体で一致する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
local notation "Q" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E)

lemma dgGluingIdentityCommaTerminalPhase_data {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R Q (n + 1))
    (y : E) (hY : s.obj (Fin.last (n + 1)) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E y)
    (β t : Fin (n + 1) →o Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData R E E (DGFunctor.id E)
        (s.pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut t)) (β ⊔ t) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData R E E (DGFunctor.id E)
        (s.pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut t)) β := by
  have hs (i : Fin (n + 1)) (hi : t i = 0) : (β ⊔ t) i = β i := by
    change max (β i) (t i) = β i
    rw [hi, max_eq_left (Fin.zero_le _)]
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSimplexData_ext_coefficients
  · intro i
    change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans.phaseObj _ _ ((β ⊔ t) i) (s.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut t i)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans.phaseObj _ _ (β i) (s.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut t i))
    by_cases hi : t i = 0
    · rw [hs i hi]
    · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut_one t i hi, hY,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPhaseObj, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPhaseObj]
  · intro I a b k hI ha hb hk
    have hab : a ≤ b := by rw [ha, hb]; exact (I.isLeast_min' _).2 (I.max'_mem _)
    by_cases hta : t a = 0
    · have hsa := hs a hta
      have he (hbs : (β ⊔ t) b = β b) :
          HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData R E E (DGFunctor.id E)
              (s.pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut t)) (β ⊔ t)).hom I a b k hI ha hb hk)
            ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData R E E (DGFunctor.id E)
              (s.pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut t)) β).hom I a b k hI ha hb hk) :=
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaPrismPhaseHom_congr R E E (DGFunctor.id E)
          (s.pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut t)) (β ⊔ t) β I a b k hI ha hb hk
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaPrismMixedHom_terminal_sup R E E (DGFunctor.id E)
            s β t I a b k hI ha hb hk)
          _ _ _ _ ((β ⊔ t).monotone hab) (β.monotone hab) hsa hbs
      by_cases htb : t b = 0
      · exact he (hs b htb)
      · have hp : ∀ p : Fin 2, p = 0 ∨ p = 1 := by decide
        rcases hp (β b) with hb0 | hb1
        · have ha0 : β a = 0 := le_antisymm (hb0 ▸ β.monotone hab) (Fin.zero_le _)
          have hsb : (β ⊔ t) b = 1 := by
            change max (β b) (t b) = 1
            have ht1 : t b = 1 := by omega
            rw [hb0, ht1]
            rfl
          have hl := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData_hom_mixed R E E (DGFunctor.id E)
            (s.pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut t)) (β ⊔ t) I a b k hI ha hb hk
            (hsa.trans ha0) hsb
          have hm := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaPrismMixedHom_terminal_sup R E E (DGFunctor.id E)
            s β t I a b k hI ha hb hk
          have hz := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaPrismMixedHom_terminal_zero R E E (DGFunctor.id E)
            (s.pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut t)) β I a b k hI ha hb hk hb0
          have hy : s.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut t b) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E y := by
            rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut_one t b htb]
            exact hY
          have hu := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaMain_coefficient R E y hy
            ((s.pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut t)).hom I a b k hI ha hb hk)
          have hr := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData_hom_zero R E E (DGFunctor.id E)
            (s.pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut t)) β I a b k hI ha hb hk ha0 hb0
          exact (hl.trans (heq_of_eq (hm.trans hz))).trans (hu.trans hr.symm)
        · apply he
          change max (β b) (t b) = β b
          rw [hb1, max_eq_left (show t b ≤ (1 : Fin 2) by omega)]
    · have hcut := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoherentPrismCut_terminal t hab hta
      have hy : s.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut t b) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E y := by
        rw [← hcut, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut_one t a hta]
        exact hY
      exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaCollapsedCoefficients R E s (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut t)
        (β ⊔ t) β I a b k hI ha hb hk hcut y hy

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
