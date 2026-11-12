module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ConeModuleQuasiIso
public import SerrePositivity.DifferentialGraded.Derived.Projective
public import SerrePositivity.DifferentialGraded.Derived.Basic

/-! 全 dg 自然な同じ円錐射を K(Gluing) の同型へ送り、円錐のホモトピー表現可能性を供給。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory CochainComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
  (p : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingConeRepresentative R C Y.left Z.left (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeLeftArrow R C D M Y Z f))
  (q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingConeRepresentative R D Y.right Z.right
    ((dgYoneda R D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeRightArrow R C D M Y Z f)))
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M
local notation "W" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeObjectFromRepresentatives R C D M Y Z f p q
local notation "yf" => CategoryTheory.Functor.map (DGFunctor.onClosed (dgYoneda R G)) f

/-- 同じ加群円錐射は、射影的加群間の準同型なので K(Gluing) で同型。 -/
lemma dgGluingConeModuleMap_isIso_homotopy :
    IsIso ((moduleToHomotopy R G).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeModuleMap R C D M Y Z f p q)) :=
  moduleHomotopicallyProjective_quasiIso_isIso_homotopy R G
    (moduleHomotopicallyProjective_cone R G (representable_homotopicallyProjective R G Y)
      (representable_homotopicallyProjective R G Z) yf)
    (representable_homotopicallyProjective R G W)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeModuleMap R C D M Y Z f p q)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeModuleMap_quasiIso R C D M Y Z f p q)

/-- 全 dg 自然な実円錐射自身を順射に持つ、代表加群との K(Gluing) 同型。 -/
def dgGluingConeModuleHomotopyIso :
    (moduleToHomotopy R G).obj (moduleCone R G yf) ≅
      (moduleToHomotopy R G).obj (ForgetEnrichment.of (Complex R) (representable R W)) := by
  letI := dgGluingConeModuleMap_isIso_homotopy R C D M Y Z f p q
  exact asIso ((moduleToHomotopy R G).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeModuleMap R C D M Y Z f p q))

include p q in
/-- 標準 Yoneda 加群円錐は、全 dg 自然な加群のホモトピー圏で表現可能。 -/
lemma dgGluingConeHomotopyRepresentable :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomotopyRepresentable R G (ForgetEnrichment.to (Complex R) (moduleCone R G yf)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty_iff R G _).2
    ⟨W, ⟨dgGluingConeModuleHomotopyIso R C D M Y Z f p q⟩⟩

omit p q in
/-- 元の両圏の前三角性から、同じ Yoneda 加群円錐の表現可能性を供給。 -/
lemma dgGluingChosenConeHomotopyRepresentable
    (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomotopyRepresentable R G (ForgetEnrichment.to (Complex R) (moduleCone R G yf)) :=
  dgGluingConeHomotopyRepresentable R C D M Y Z f
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingChooseConeRepresentative R C Y.left Z.left
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeLeftArrow R C D M Y Z f) hC)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingChooseConeRepresentative R D Y.right Z.right
      ((dgYoneda R D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeRightArrow R C D M Y Z f)) hD)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
