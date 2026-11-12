module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.KernelRepresentativeHomotopy
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.KernelHomProjections

/-! 元の gluing Hom 円錐を、選んだ同じ gluing 円錐対象への native Hom と点ごとに比較する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory HomologicalComplex CochainComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
  (p : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingConeRepresentative R C Y.left Z.left (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeLeftArrow R C D M Y Z f))
  (q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingConeRepresentative R D Y.right Z.right
    ((dgYoneda R D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeRightArrow R C D M Y Z f)))
local notation "W" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeObjectFromRepresentatives R C D M Y Z f p q

/-- 元の Hom 円錐と同じ代表 gluing 対象への native Hom との、点ごとの実ホモトピー同値。 -/
def dgGluingHomConeNativeRepresentativeEquiv :
    HomotopyEquiv (mappingCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcomposition R C D M X Y Z f))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X W) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeKernelRepresentativeEquiv R C D M Y Z f p q X).trans
    (HomotopyEquiv.ofIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomIso R C D M X W).symm)

/-- 順射は、標準 Hom 円錐比較・同じ代表射による後合成・同じ native 比較の逆の合成。 -/
lemma dgGluingHomConeNativeRepresentativeEquiv_hom :
    (dgGluingHomConeNativeRepresentativeEquiv R C D M X Y Z f p q).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeKernelIso R C D M X Y Z f).hom ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeRepresentativePost R C D M Y Z f p q
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelObject R C D M X) ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomIso R C D M X W).inv := by
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeKernelRepresentativeEquiv R C D M Y Z f p q X).hom ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomIso R C D M X W).inv = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeKernelRepresentativeEquiv_hom, Category.assoc]

omit p q in
/-- 元の両圏の前三角性から選んだ同じ対象に、各試験対象で native Hom 円錐を移す。 -/
def dgGluingHomConeNativeEquiv (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D) :
    HomotopyEquiv (mappingCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcomposition R C D M X Y Z f))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeObject R C D M Y Z f hC hD)) :=
  dgGluingHomConeNativeRepresentativeEquiv R C D M X Y Z f
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingChooseConeRepresentative R C Y.left Z.left (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeLeftArrow R C D M Y Z f) hC)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingChooseConeRepresentative R D Y.right Z.right
      ((dgYoneda R D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeRightArrow R C D M Y Z f)) hD)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
