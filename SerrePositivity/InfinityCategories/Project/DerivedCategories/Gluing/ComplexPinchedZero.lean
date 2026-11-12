module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexPinchedModel

/-! 零複体の実空間模型への射は、元の全線形成分の一意性から一意。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CochainComplex HomComplex DifferentialGraded
open scoped ZeroObject _root_.Simplicial
variable {R : Type u} [CommRing R]

lemma dgGluingComplexPinchedZero_subsingleton (n : SimplexCategoryᵒᵖ) :
    Subsingleton ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, v} (0 : Complex R)).obj n) := by
  refine ⟨fun s t => ?_⟩
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.linearEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSource.{u, v} (0 : Complex R))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedTarget.{u, v} (0 : Complex R)) n.unop.len).injective
  apply Subtype.ext
  funext i
  apply Cochain.ext
  intro p q hpq
  change (_ : (𝟙_ (_root_.SerrePositivity.DifferentialGraded.Complex R)).X p ⟶ (0 : _root_.SerrePositivity.DifferentialGraded.Complex R).X q) = _
  exact ((HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) q).map_isZero
    (Limits.isZero_zero (_root_.SerrePositivity.DifferentialGraded.Complex R))).eq_of_tgt _ _

lemma dgGluingComplexPinchedZero_hom_ext {T : SSet.{max u v}}
    (f g : T ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, v} (0 : Complex R)) : f = g := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro t
  let := dgGluingComplexPinchedZero_subsingleton.{u, v} (R := R) n
  exact Subsingleton.elim _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
