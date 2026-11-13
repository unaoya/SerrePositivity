module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.KernelComparisonConeData
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.KernelComparisonHomIso

/-! 直接 dg 関手の対象型を保持する、同じ円錐比較・指定境界元・実代表射。 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
local notation "E" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R (RightModule R D) (RightModule R C)
  (Morita.kernelTensor R D C M)
local notation "F" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelComparisonFunctor R C D M
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeObject R C D M Y Z f

/-- 同じ標準 Hom 円錐同型を、関手の対象の Hom 型に固定。 -/
def dgGluingKernelComparisonConeIso (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    mappingCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcomposition R C D M X Y Z f) ≅
      homObject R E ((F).obj X) L := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeKernelIso R C D M X Y Z f

/-- native の始域 Hom 型を固定した、同じ標準円錐左包含。 -/
def dgGluingKernelComparisonConeInl (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    Cochain (homObject R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) X Y)
      (mappingCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcomposition R C D M X Y Z f)) (-1) :=
  mappingCone.inl (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcomposition R C D M X Y Z f)

/-- 同じ指定境界元を、関手の対象の斉次 Hom 型に固定。 -/
def dgGluingKernelComparisonNullElement : GradedHom R ((F).obj Y) L (-1) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeNullElement R C D M Y Z f

variable
  (p : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingConeRepresentative R C Y.left Z.left (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeLeftArrow R C D M Y Z f))
  (q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingConeRepresentative R D Y.right Z.right
    ((dgYoneda R D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeRightArrow R C D M Y Z f)))
local notation "W" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeObjectFromRepresentatives R C D M Y Z f p q

/-- native の斉次 Hom 型を固定した、同じ指定境界元。 -/
def dgGluingKernelComparisonNativeNullElement : GradedHom R Y W (-1) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeNullElement R C D M Y Z f p q

/-- 同じ実代表射を、関手の対象を終域に持つ閉射として固定。 -/
def dgGluingKernelComparisonRepresentativeMap :
    ForgetEnrichment.of (Complex R) L ⟶ ForgetEnrichment.of (Complex R) ((F).obj W) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeRepresentativeMap R C D M Y Z f p q

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
