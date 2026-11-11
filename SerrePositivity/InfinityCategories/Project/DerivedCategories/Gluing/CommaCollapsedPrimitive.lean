module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCommaAugPrismData
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex

/-! 単調写像で両端が潰れる全係数では、実 comma primitive は厳密に零。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded MonoidalCategory
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E)

lemma dgGluingCommaPrimitive_unitElement (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyComponent R C E F X X 0 (unitElement R X).val = 0 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyComponent_unit R C E F X 0 _

lemma dgGluingCommaPrimitive_of_unit
    {X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F} {k : ℤ} (f : GradedHom R X Y k)
    (hXY : X = Y) (hk : k = 0) (hf : HEq f (_root_.SerrePositivity.DifferentialGraded.unitElement R Y).val) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyComponent R C E F X Y k f = 0 := by
  cases hXY
  subst k
  rw [eq_of_heq hf]
  exact dgGluingCommaPrimitive_unitElement R C E F X

lemma dgGluingCommaPrimitive_pullback_collapsed
    {m n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) n)
    (α : Fin (m + 1) →o Fin (n + 1)) (I : Finset (Fin (m + 1)))
    (a b : Fin (m + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hab : α a = α b) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyComponent R C E F
      ((s.pullback α).obj a) ((s.pullback α).obj b) k
      ((s.pullback α).hom I a b k hI ha hb hk) = 0 := by
  have haI : a ∈ I := ha ▸ I.min'_mem (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)
  have hbI : b ∈ I := hb ▸ I.max'_mem (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)
  have hlt : a < b := by
    rw [ha, hb]
    exact I.min'_lt_max'_of_card (by omega)
  have hi : ¬ Set.InjOn α (I : Set (Fin (m + 1))) := by
    intro h
    exact (ne_of_lt hlt) (h haI hbI hab)
  by_cases hc : I.card = 2
  · exact dgGluingCommaPrimitive_of_unit R C E F _ (congrArg s.obj hab)
      (by omega) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_collapsed_pair s α I a b k hI ha hb hk hi hc)
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_not_inj s α I a b k hI ha hb hk hi hc]
    exact map_zero (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F _ _).v k (k - 1) (by omega)).hom)

lemma dgGluingCommaPrismCut_pullback_collapsed
    {m n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) n)
    (α : Fin (m + 1) →o Fin (n + 1)) (I : Finset (Fin (m + 1)))
    (a b : Fin (m + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (j : Fin (m + 1))
    (hj : j ∈ I) (haj : a < j) (hjb : j < b) (hα : α j = α b) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismCut R C E F (s.pullback α)
      I a b k hI ha hb hk j hj haj hjb = 0 := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismCut]
  rw [dgGluingCommaPrimitive_pullback_collapsed R C E F s α _ _ _ _ _ _ _ rfl hα,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, smul_zero]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
