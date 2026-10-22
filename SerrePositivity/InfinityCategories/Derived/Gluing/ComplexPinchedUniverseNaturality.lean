module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexPinchedUniverseIso

/-! 対象宇宙の変更は、元の同じ全鎖写像の pinched 空間作用と厳密に可換。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve.PinchedHom
open scoped Simplicial
variable {R : Type u} [CommRing R] {K L : Complex R}

lemma dgGluingComplexPinchedUniverseIso_naturality (φ : K ⟶ L) :
    (SSet.uliftFunctor.{max u v w, max u v}).map (complexPinchedMap.{u, v} φ) ≫
        (dgGluingComplexPinchedUniverseIso.{u, v, w} L).hom =
      (dgGluingComplexPinchedUniverseIso.{u, v, w} K).hom ≫
        (SSet.uliftFunctor.{max u v w, max u w}).map (complexPinchedMap.{u, w} φ) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply ULift.ext
  apply (linearEquiv (complexPinchedSource.{u, w} L)
    (complexPinchedTarget.{u, w} L) n.unop.len).injective
  change toLinearSimplex
      (dgGluingComplexPinchedUniverseEquiv.{u, v, w} L n.unop.len
        (pinchedHomChainMapSimplex _ s.down)) =
    toLinearSimplex (pinchedHomChainMapSimplex _
      (dgGluingComplexPinchedUniverseEquiv.{u, v, w} K n.unop.len s.down))
  rw [dgGluingComplexPinchedUniverseEquiv_linear, pinchedHomChainMapSimplex_linear,
    pinchedHomChainMapSimplex_linear, dgGluingComplexPinchedUniverseEquiv_linear]
  rfl

end SerrePositivity.InfinityCategories
