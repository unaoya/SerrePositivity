module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ConeObject
public import SerrePositivity.InfinityCategories.Derived.Gluing.FactorSubcategories

/-! 右射影で同型となる閉 gluing 射の実円錐は、C 充満因子に属する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits Pretriangulated DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (A B : DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) A ⟶ ForgetEnrichment.of (Complex R) B)
  (hC : IsDGPretriangulated R C) (hD : IsDGPretriangulated R D)

/-- 同じ右成分の H⁰ 同型から、選んだ円錐代表の右成分のホモトピー零性を導く。 -/
lemma dgGluingConeObject_right_zero_of_isIso
    (hf : IsIso ((toHomotopy R D).map (dgGluingConeRightArrow R C D M A B f))) :
    dgGluingFactorIsZero R D (dgGluingConeObject R C D M A B f hC hD).right := by
  let g := (dgYoneda R D).onClosed.map (dgGluingConeRightArrow R C D M A B f)
  have hg : IsIso ((moduleToHomotopy R D).map g) := by
    have := hf
    change IsIso ((dgYoneda R D).onHomotopy.map
      ((toHomotopy R D).map (dgGluingConeRightArrow R C D M A B f)))
    infer_instance
  have hz : IsZero ((moduleToHomotopy R D).obj (moduleCone R D g)) :=
    Triangle.isZero₃_of_isIso₁ (moduleHomotopyConeTriangle R D g)
      (moduleHomotopyConeTriangle_distinguished R D g) hg
  apply (dgGluingFactorIsZero_iff_representable R D _).2
  exact hz.of_iso (dgGluingConeObject_rightIso R C D M A B f hC hD).symm

end SerrePositivity.InfinityCategories
