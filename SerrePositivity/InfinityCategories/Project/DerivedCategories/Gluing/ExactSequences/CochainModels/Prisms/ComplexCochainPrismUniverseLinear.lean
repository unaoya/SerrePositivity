module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CochainModels.Prisms.CochainPrismUniverseComponents
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomotopyRepresentations.ComplexCochainAugmentationHomotopy
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CochainModels.Cochains.CommonComplexUniverseIso

/-! 任意対象宇宙の複体 cochain prism は、canonical 宇宙変更で全線形成分を保つ。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded CochainComplex HomComplex MonoidalCategory

open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {K L : _root_.SerrePositivity.DifferentialGraded.Complex R}
  (f g : K ⟶ L) (h : Cochain K L (-1)) (he : δ (-1) 0 h = Cochain.ofHom (g - f))

lemma dgGluingComplexCochainPrism_universe_linear {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max u v} K) _⦋n⦌) (β : Fin (n + 1) →o Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPinchedPrismSimplex R
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGComplexPinchedModel.{u, max u v} L)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaPinchedInput.{u, v} R
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGComplexPinchedModel.{u, max u v} L) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSource L) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedTarget L)
        K (f ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso L).hom) (g ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso L).hom)
        (h.comp (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso L).hom) (add_zero (-1)))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainUnitHom_boundary f g h he)).app (Opposite.op ⦋n⦌) s) β) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPinchedPrismSimplex R
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGComplexPinchedModel.{u, max u w} L)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaPinchedInput.{u, w} R
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGComplexPinchedModel.{u, max u w} L) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSource L) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedTarget L)
          K (f ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso L).hom) (g ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso L).hom)
          (h.comp (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso L).hom) (add_zero (-1)))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainUnitHom_boundary f g h he)).app (Opposite.op ⦋n⦌)
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedUniverseEquiv.{u, max u v, max u w} K n s)) β) := by
  apply Subtype.ext
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  have hs : ∀ J p hJ hp, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData s).component J p hJ hp =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedUniverseEquiv.{u, max u v, max u w} K n s)).component
        J p hJ hp := by
    intro J p hJ hp
    exact congrArg (fun z : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSource.{u, max u w} K)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedTarget.{u, max u w} K) n => z.val.component J p hJ hp)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedUniverseEquiv_linear.{u, max u v, max u w} K s).symm
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainPrism_universe_component.{u, v, w} R
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGComplexPinchedModel.{u, max u v} L) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGComplexPinchedModel.{u, max u w} L)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSource L) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedTarget L)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSource L) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedTarget L) K
    (f ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso L).hom) (g ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso L).hom)
    (h.comp (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso L).hom) (add_zero (-1)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainUnitHom_boundary f g h he)
    (f ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso L).hom) (g ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso L).hom)
    (h.comp (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso L).hom) (add_zero (-1)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainUnitHom_boundary f g h he) (𝟙 _)
    (Category.comp_id _) (Category.comp_id _) (Cochain.comp_id _)
    s (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedUniverseEquiv.{u, max u v, max u w} K n s) hs β J k hJ hk

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
