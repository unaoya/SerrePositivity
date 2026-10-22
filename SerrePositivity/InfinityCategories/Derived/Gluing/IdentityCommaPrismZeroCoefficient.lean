module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaObject
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaPrismZeroPhase

/-! 標的の augmentation が恒等なら、相零の混合主項も同じ replacement 係数になる。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.HomotopyComparison
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E]

lemma dgGluingIdentityCommaAugmentation_unit
    (Z : DGFunctorCommaObject R E E (DGFunctor.id E)) (y : E)
    (hZ : Z = dgGluingIdentityCommaObject R E y) :
    HEq (dgCommaAugmentationComponent R E E (DGFunctor.id E) Z).val
      (unitElement R Z.source).val := by
  subst Z
  apply heq_of_eq
  change (closedHomEquiv R E _ _ (𝟙 (ForgetEnrichment.of (Complex R) y))).val = _
  rw [closedHom_id]
  rfl

lemma dgGluingIdentityCommaPrismMain_target {n : ℕ}
    (s : SimplexData R (DGFunctorCommaObject R E E (DGFunctor.id E)) (n + 1))
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (y : E) (hy : s.obj b = dgGluingIdentityCommaObject R E y) :
    HEq (dgGluingCommaPrismMainCoefficient R E E (DGFunctor.id E) s I a b k hI ha hb hk)
      (((dgCommaAugmentationSource R E E (DGFunctor.id E)).map (s.obj a) (s.obj b)).f k
        (s.hom I a b k hI ha hb hk)) := by
  dsimp only [dgGluingCommaPrismMainCoefficient]
  apply unit_compose_of_heq
  · change (s.obj b).replacement = (s.obj b).source
    rw [hy]
  · rfl
  · exact dgGluingIdentityCommaAugmentation_unit R E (s.obj b) y hy

lemma dgGluingIdentityCommaPrismMixed_target {n : ℕ}
    (s : SimplexData R (DGFunctorCommaObject R E E (DGFunctor.id E)) (n + 1))
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (y : E) (hy : s.obj b = dgGluingIdentityCommaObject R E y) :
    HEq (dgCommaAugmentationPrismMixedHom R E E (DGFunctor.id E) s
      (pinchedPrismPhase (OrderHom.const (Fin (n + 1)) (0 : Fin 2))) I a b k hI ha hb hk)
      (((dgCommaAugmentationSource R E E (DGFunctor.id E)).map (s.obj a) (s.obj b)).f k
        (s.hom I a b k hI ha hb hk)) := by
  exact (heq_of_eq (dgGluingCommaPrismMixedHom_zeroPhase R E E (DGFunctor.id E) s
    I a b k hI ha hb hk)).trans
      (dgGluingIdentityCommaPrismMain_target R E s I a b k hI ha hb hk y hy)

end SerrePositivity.InfinityCategories
