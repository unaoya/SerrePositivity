module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Objects.IdentityCommaObject
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.PinchedPrismPhase
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedComponents

/-! 恒等 augmentation の二対象間では、元の全 prism 自身が固定二端の pinched Hom に入る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded SSet MonoidalCategory
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
  {x y : E} {n : ℕ}
  (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E x) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E y)) _⦋n⦌)

def dgGluingIdentityCommaPinchedPrismSimplex (β : Fin (n + 1) →o Fin 2) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R E x y) _⦋n⦌ where
  val := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex R E E (DGFunctor.id E) s.val (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase β)
  source := by
    change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex R E E (DGFunctor.id E) s.val
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase β)).pullback Fin.castSuccOrderEmb.toOrderHom = _
    have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex_pullback R E E (DGFunctor.id E) s.val
      Fin.castSuccOrderEmb.toOrderHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase β)
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase_front] at h
    have hs : s.val.pullback Fin.castSuccOrderEmb.toOrderHom =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
          (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E)))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E x)) n := s.source
    exact h.symm.trans ((congrArg (fun t =>
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex R E E (DGFunctor.id E) t β) hs).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPrism_constant R E x β))
  target := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv (A := R) (D := E)).injective
    change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans.phaseObj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R E E (DGFunctor.id E))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationTarget R E E (DGFunctor.id E))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase β (Fin.last (n + 1))) (s.val.obj (Fin.last (n + 1))) = y
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase_last, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.target_obj s]
    rfl

lemma dgGluingIdentityCommaPinchedPrismSimplex_naturality {m : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (β : Fin (n + 1) →o Fin 2) :
    (dgGluingIdentityCommaPinchedPrismSimplex R E s β).pullback α =
      dgGluingIdentityCommaPinchedPrismSimplex R E (s.pullback α) (β.comp α.toOrderHom) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex R E E (DGFunctor.id E) s.val
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase β)).pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α.toOrderHom) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex R E E (DGFunctor.id E)
      (s.val.pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α.toOrderHom))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase (β.comp α.toOrderHom))
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex_pullback]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
