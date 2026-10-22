module
public import SerrePositivity.InfinityCategories.Derived.ComplexPinchedModel

/-! 零複体の実空間模型への射は、元の全線形成分の一意性から一意。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CochainComplex HomComplex DifferentialGraded DGNerve.PinchedHom
open scoped ZeroObject Simplicial
variable {R : Type u} [CommRing R]

lemma dgGluingComplexPinchedZero_subsingleton (n : SimplexCategoryᵒᵖ) :
    Subsingleton ((complexPinchedSpace.{u, v} (0 : Complex R)).obj n) := by
  refine ⟨fun s t => ?_⟩
  apply (linearEquiv (complexPinchedSource.{u, v} (0 : Complex R))
    (complexPinchedTarget.{u, v} (0 : Complex R)) n.unop.len).injective
  apply Subtype.ext
  funext i
  apply Cochain.ext
  intro p q hpq
  change (_ : (𝟙_ (Complex R)).X p ⟶ (0 : Complex R).X q) = _
  exact ((HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) q).map_isZero
    (Limits.isZero_zero (Complex R))).eq_of_tgt _ _

lemma dgGluingComplexPinchedZero_hom_ext {T : SSet.{max u v}}
    (f g : T ⟶ complexPinchedSpace.{u, v} (0 : Complex R)) : f = g := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro t
  let := dgGluingComplexPinchedZero_subsingleton.{u, v} (R := R) n
  exact Subsingleton.elim _ _

end SerrePositivity.InfinityCategories
