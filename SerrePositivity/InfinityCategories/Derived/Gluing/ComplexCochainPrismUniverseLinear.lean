module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CochainPrismUniverseComponents
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexCochainAugmentationHomotopy
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommonComplexUniverseIso

/-! 任意対象宇宙の複体 cochain prism は、canonical 宇宙変更で全線形成分を保つ。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex MonoidalCategory
open DGNerve DGNerve.PinchedHom
open scoped Simplicial
variable {R : Type u} [CommRing R] {K L : Complex R}
  (f g : K ⟶ L) (h : Cochain K L (-1)) (he : δ (-1) 0 h = Cochain.ofHom (g - f))

lemma dgGluingComplexCochainPrism_universe_linear {n : ℕ}
    (s : (complexPinchedSpace.{u, max u v} K) _⦋n⦌) (β : Fin (n + 1) →o Fin 2) :
    toLinearSimplex (dgGluingIdentityCommaPinchedPrismSimplex R
      (DGComplexPinchedModel.{u, max u v} L)
      ((dgGluingCochainIdentityCommaPinchedInput.{u, v} R
        (DGComplexPinchedModel.{u, max u v} L) (complexPinchedSource L) (complexPinchedTarget L)
        K (f ≫ (complexUnitHomIso L).hom) (g ≫ (complexUnitHomIso L).hom)
        (h.comp (Cochain.ofHom (complexUnitHomIso L).hom) (add_zero (-1)))
        (dgGluingCochainUnitHom_boundary f g h he)).app (Opposite.op ⦋n⦌) s) β) =
      toLinearSimplex (dgGluingIdentityCommaPinchedPrismSimplex R
        (DGComplexPinchedModel.{u, max u w} L)
        ((dgGluingCochainIdentityCommaPinchedInput.{u, w} R
          (DGComplexPinchedModel.{u, max u w} L) (complexPinchedSource L) (complexPinchedTarget L)
          K (f ≫ (complexUnitHomIso L).hom) (g ≫ (complexUnitHomIso L).hom)
          (h.comp (Cochain.ofHom (complexUnitHomIso L).hom) (add_zero (-1)))
          (dgGluingCochainUnitHom_boundary f g h he)).app (Opposite.op ⦋n⦌)
            (dgGluingComplexPinchedUniverseEquiv.{u, max u v, max u w} K n s)) β) := by
  apply Subtype.ext
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  have hs : ∀ J p hJ hp, (toLinearData s).component J p hJ hp =
      (toLinearData (dgGluingComplexPinchedUniverseEquiv.{u, max u v, max u w} K n s)).component
        J p hJ hp := by
    intro J p hJ hp
    exact congrArg (fun z : LinearSimplex R (complexPinchedSource.{u, max u w} K)
      (complexPinchedTarget.{u, max u w} K) n => z.val.component J p hJ hp)
      (dgGluingComplexPinchedUniverseEquiv_linear.{u, max u v, max u w} K s).symm
  exact dgGluingCochainPrism_universe_component.{u, v, w} R
    (DGComplexPinchedModel.{u, max u v} L) (DGComplexPinchedModel.{u, max u w} L)
    (complexPinchedSource L) (complexPinchedTarget L)
    (complexPinchedSource L) (complexPinchedTarget L) K
    (f ≫ (complexUnitHomIso L).hom) (g ≫ (complexUnitHomIso L).hom)
    (h.comp (Cochain.ofHom (complexUnitHomIso L).hom) (add_zero (-1)))
    (dgGluingCochainUnitHom_boundary f g h he)
    (f ≫ (complexUnitHomIso L).hom) (g ≫ (complexUnitHomIso L).hom)
    (h.comp (Cochain.ofHom (complexUnitHomIso L).hom) (add_zero (-1)))
    (dgGluingCochainUnitHom_boundary f g h he) (𝟙 _)
    (Category.comp_id _) (Category.comp_id _) (Cochain.comp_id _)
    s (dgGluingComplexPinchedUniverseEquiv.{u, max u v, max u w} K n s) hs β J k hJ hk

end SerrePositivity.InfinityCategories
