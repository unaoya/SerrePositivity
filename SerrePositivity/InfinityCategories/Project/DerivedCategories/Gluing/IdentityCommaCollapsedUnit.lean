module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.IdentityCommaObject
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CommaCollapsedPhase

/-! 恒等 augmentation 頂点へ潰れる二点の係数は、任意の端点相で元の単位。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
local notation "Q" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E)

lemma dgGluingIdentityCommaPhaseObj (y : E) (p : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans.phaseObj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R E E (DGFunctor.id E))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationTarget R E E (DGFunctor.id E)) p
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E y) = y := by
  fin_cases p <;> rfl

lemma dgGluingIdentityCommaUnitMain {X Y : Q} (y : E)
    (f : GradedHom R X Y 0) (hXY : X = Y) (hY : Y = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E y)
    (hf : HEq f (_root_.SerrePositivity.DifferentialGraded.unitElement R Y).val) :
    HEq (compose R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationComponent R E E (DGFunctor.id E) Y).val
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R E E (DGFunctor.id E)).map X Y).f 0 f)
      (add_zero 0)) (_root_.SerrePositivity.DifferentialGraded.unitElement R y).val := by
  subst X
  subst Y
  rw [eq_of_heq hf, _root_.SerrePositivity.DifferentialGraded.DGFunctor.map_unitElement]
  change HEq (_root_.SerrePositivity.DifferentialGraded.compose R (_root_.SerrePositivity.DifferentialGraded.unitElement R y).val (_root_.SerrePositivity.DifferentialGraded.unitElement R y).val (add_zero 0)) _
  exact heq_of_eq (_root_.SerrePositivity.DifferentialGraded.unit_compose R _)

lemma dgGluingIdentityCommaCollapsedPhase_unit
    {m n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R Q n)
    (α : Fin (m + 1) →o Fin (n + 1)) (β : Fin (m + 1) →o Fin 2)
    (I : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : (0 : ℤ) = 2 - (I.card : ℤ)) (hc : I.card = 2) (hab : α a = α b)
    (y : E) (hY : s.obj (α b) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E y)
    (p q : Fin 2) (hpq : p ≤ q) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismPhaseHom R E E (DGFunctor.id E) (s.pullback α) β
      I a b 0 hI ha hb hk p q hpq) (_root_.SerrePositivity.DifferentialGraded.unitElement R y).val := by
  have haI : a ∈ I := ha ▸ I.min'_mem (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)
  have hbI : b ∈ I := hb ▸ I.max'_mem (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)
  have hlt : a < b := by rw [ha, hb]; exact I.min'_lt_max'_of_card (by omega)
  have hi : ¬ Set.InjOn α (I : Set (Fin (m + 1))) := by
    intro h
    exact (ne_of_lt hlt) (h haI hbI hab)
  have hf := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_collapsed_pair s α I a b 0 hI ha hb hk hi hc
  have ho : ∀ (H : _root_.SerrePositivity.DifferentialGraded.DGFunctor R Q E), H.obj (s.obj (α b)) = y →
      HEq ((H.map (s.obj (α a)) (s.obj (α b))).f 0
        ((s.pullback α).hom I a b 0 hI ha hb hk)) (_root_.SerrePositivity.DifferentialGraded.unitElement R y).val := by
    intro H hH
    have hu := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.map_unit_of_heq H ((s.pullback α).hom I a b 0 hI ha hb hk)
      (congrArg s.obj hab) hf
    have he : HEq (_root_.SerrePositivity.DifferentialGraded.unitElement R (H.obj (s.obj (α b)))).val (_root_.SerrePositivity.DifferentialGraded.unitElement R y).val := by
      cases hH
      rfl
    exact hu.trans he
  fin_cases p <;> fin_cases q
  · exact ho (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R E E (DGFunctor.id E))
      (by rw [hY]; rfl)
  · change HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismMixedHom R E E (DGFunctor.id E)
      (s.pullback α) β I a b 0 hI ha hb hk) _
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismMixedHom_two R E E (DGFunctor.id E)
      (s.pullback α) β I a b 0 hI ha hb hk hc]
    exact dgGluingIdentityCommaUnitMain R E y _ (congrArg s.obj hab) hY hf
  · change (1 : ℕ) ≤ 0 at hpq
    omega
  · exact ho (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationTarget R E E (DGFunctor.id E))
      (by rw [hY]; rfl)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
