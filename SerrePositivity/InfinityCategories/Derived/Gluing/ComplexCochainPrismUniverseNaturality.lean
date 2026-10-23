module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexCochainPrismUniverseLinear
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseSimplexFamilies

/-! 同じ複体 cochain prism の全時間族は、canonical な対象宇宙変更と可換。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w r
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex MonoidalCategory SSet
open DGNerve DGNerve.PinchedHom
open scoped Simplicial
variable {R : Type u} [CommRing R] {K L : Complex R}
  (f g : K ⟶ L) (h : Cochain K L (-1)) (he : δ (-1) 0 h = Cochain.ofHom (g - f))

lemma dgGluingComplexCochainPrism_universe_naturality :
    dgGluingUliftSimplexFamily.{max u v, max u v w r} 1
        (dgGluingComplexCochainAugmentationPrism.{u, v} f g h he) ≫
      (dgGluingCommonComplexPinchedUniverseIso.{u, max u v, max u w, r} L).hom =
      (Δ[1] ◁ (dgGluingCommonComplexPinchedUniverseIso.{u, max u v, max u w, r} K).hom) ≫
        dgGluingUliftSimplexFamily.{max u w, max u v w r} 1
          (dgGluingComplexCochainAugmentationPrism.{u, w} f g h he) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨β, s⟩
  apply ULift.ext
  apply (linearEquiv (complexPinchedSource.{u, max u w} L)
    (complexPinchedTarget.{u, max u w} L) n).injective
  change toLinearSimplex
      (dgGluingComplexPinchedUniverseEquiv.{u, max u v, max u w} L n
        ((dgGluingComplexCochainAugmentationPrism.{u, v} f g h he).app (Opposite.op ⦋n⦌)
          (ULift.up β.down, s.down))) =
    toLinearSimplex
      ((dgGluingComplexCochainAugmentationPrism.{u, w} f g h he).app (Opposite.op ⦋n⦌)
        (ULift.up β.down, dgGluingComplexPinchedUniverseEquiv.{u, max u v, max u w} K n s.down))
  rw [dgGluingComplexPinchedUniverseEquiv_linear]
  exact dgGluingComplexCochainPrism_universe_linear.{u, v, w} f g h he s.down
    (stdSimplex.objEquiv β).toOrderHom

end SerrePositivity.InfinityCategories
