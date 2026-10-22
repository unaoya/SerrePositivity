module
public import SerrePositivity.InfinityCategories.Derived.Gluing.KernelRepresentativeHomotopy
public import SerrePositivity.InfinityCategories.Derived.Gluing.KernelHomProjections

/-! 元の gluing Hom 円錐を、選んだ同じ gluing 円錐対象への native Hom と点ごとに比較する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory HomologicalComplex CochainComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X Y Z : DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
  (p : DGGluingConeRepresentative R C Y.left Z.left (dgGluingConeLeftArrow R C D M Y Z f))
  (q : DGGluingConeRepresentative R D Y.right Z.right
    ((dgYoneda R D).onClosed.map (dgGluingConeRightArrow R C D M Y Z f)))
local notation "W" => dgGluingConeObjectFromRepresentatives R C D M Y Z f p q

/-- 元の Hom 円錐と同じ代表 gluing 対象への native Hom との、点ごとの実ホモトピー同値。 -/
def dgGluingHomConeNativeRepresentativeEquiv :
    HomotopyEquiv (mappingCone (dgGluingPostcomposition R C D M X Y Z f))
      (dgGluingHomComplex R C D M X W) :=
  (dgGluingHomConeKernelRepresentativeEquiv R C D M Y Z f p q X).trans
    (HomotopyEquiv.ofIso (dgGluingKernelHomIso R C D M X W).symm)

/-- 順射は、標準 Hom 円錐比較・同じ代表射による後合成・同じ native 比較の逆の合成。 -/
lemma dgGluingHomConeNativeRepresentativeEquiv_hom :
    (dgGluingHomConeNativeRepresentativeEquiv R C D M X Y Z f p q).hom =
    (dgGluingHomConeKernelIso R C D M X Y Z f).hom ≫
      dgGluingKernelConeRepresentativePost R C D M Y Z f p q
        (dgGluingKernelObject R C D M X) ≫ (dgGluingKernelHomIso R C D M X W).inv := by
  change (dgGluingHomConeKernelRepresentativeEquiv R C D M Y Z f p q X).hom ≫
    (dgGluingKernelHomIso R C D M X W).inv = _
  rw [dgGluingHomConeKernelRepresentativeEquiv_hom, Category.assoc]

omit p q in
/-- 元の両圏の前三角性から選んだ同じ対象に、各試験対象で native Hom 円錐を移す。 -/
def dgGluingHomConeNativeEquiv (hC : IsDGPretriangulated R C) (hD : IsDGPretriangulated R D) :
    HomotopyEquiv (mappingCone (dgGluingPostcomposition R C D M X Y Z f))
      (dgGluingHomComplex R C D M X (dgGluingConeObject R C D M Y Z f hC hD)) :=
  dgGluingHomConeNativeRepresentativeEquiv R C D M X Y Z f
    (dgGluingChooseConeRepresentative R C Y.left Z.left (dgGluingConeLeftArrow R C D M Y Z f) hC)
    (dgGluingChooseConeRepresentative R D Y.right Z.right
      ((dgYoneda R D).onClosed.map (dgGluingConeRightArrow R C D M Y Z f)) hD)

end SerrePositivity.InfinityCategories
