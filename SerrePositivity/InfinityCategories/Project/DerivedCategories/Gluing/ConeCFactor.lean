module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ConeObject
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.FactorSubcategories

/-! 右射影で同型となる閉 gluing 射の実円錐は、C 充満因子に属する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits Pretriangulated DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (A B : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) A ⟶ ForgetEnrichment.of (Complex R) B)
  (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D)

/-- 同じ右成分の H⁰ 同型から、選んだ円錐代表の右成分のホモトピー零性を導く。 -/
lemma dgGluingConeObject_right_zero_of_isIso
    (hf : IsIso ((toHomotopy R D).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeRightArrow R C D M A B f))) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFactorIsZero R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeObject R C D M A B f hC hD).right := by
  let g := (dgYoneda R D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeRightArrow R C D M A B f)
  have hg : IsIso ((moduleToHomotopy R D).map g) := by
    have := hf
    change IsIso ((dgYoneda R D).onHomotopy.map
      ((toHomotopy R D).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeRightArrow R C D M A B f)))
    infer_instance
  have hz : IsZero ((moduleToHomotopy R D).obj (moduleCone R D g)) :=
    Triangle.isZero₃_of_isIso₁ (moduleHomotopyConeTriangle R D g)
      (moduleHomotopyConeTriangle_distinguished R D g) hg
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFactorIsZero_iff_representable R D _).2
  exact hz.of_iso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeObject_rightIso R C D M A B f hC hD).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
