module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.FactorZeroTransport
public import SerrePositivity.DifferentialGraded.Category.Tensor
public import SerrePositivity.HomologicalAlgebra.Complex.ConeLES
public import SerrePositivity.DifferentialGraded.Bimodule.Basic

/-! ホモトピー零の実 Hom 複体と双加群の値から、全次数の acyclic 性を回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits HomologicalComplex DifferentialGraded
variable (R : Type u) [CommRing R]

lemma dgGluingFactorIsZero_complex_acyclic (K : Complex R)
    (hK : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFactorIsZero R (Complex R) K) : K.Acyclic := by
  have hk : IsZero ((_root_.HomotopyCategory.quotient
      (ModuleCat R) (ComplexShape.up ℤ)).obj K) :=
    (complexHomotopyComparison R).map_isZero hK
  exact (_root_.HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic K).1
    ((_root_.HomotopyCategory.subcategoryAcyclic (ModuleCat R)).prop_of_isZero hk)

variable (C : Type v) [DGCategory R C]

lemma dgGluingHom_acyclic_of_target_zero (x y : C) (hy : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFactorIsZero R C y) :
    (homObject R C x y).Acyclic :=
  dgGluingFactorIsZero_complex_acyclic R _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFactorIsZero_hom_target R C x y hy)

lemma dgGluingHom_acyclic_of_source_zero (x y : C) (hx : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFactorIsZero R C x) :
    (homObject R C x y).Acyclic :=
  dgGluingFactorIsZero_complex_acyclic R _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFactorIsZero_hom_source R C x y hx)

variable [Small.{u} C] (D : Type w) [DGCategory R D] (M : Bimodule R C D)

/-- 第二変数がホモトピー零なら、元の双加群の値そのものが acyclic。 -/
lemma dgGluingBimodule_acyclic_of_right_zero (c : C) (d : D)
    (hd : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFactorIsZero R D d) : (M.value c d).Acyclic :=
  dgGluingFactorIsZero_complex_acyclic R _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFactorIsZero_map R D (M.leftAt c) d hd)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
