module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ConeModuleMapEvaluation

/-! 指定した native 境界元を kernel 表示へ戻し、全次数の後合成の比較も回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory HomologicalComplex CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (Y Z : DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
  (p : DGGluingConeRepresentative R C Y.left Z.left (dgGluingConeLeftArrow R C D M Y Z f))
  (q : DGGluingConeRepresentative R D Y.right Z.right
    ((dgYoneda R D).onClosed.map (dgGluingConeRightArrow R C D M Y Z f)))
local notation "G" => DGGluingObject R C D M
local notation "E" => DGFunctorCommaObject R (RightModule R D) (RightModule R C)
  (Morita.kernelTensor R D C M)
local notation "KY" => dgGluingKernelObject R C D M Y
local notation "W" => dgGluingConeObjectFromRepresentatives R C D M Y Z f p q
local notation "L" => dgGluingKernelConeObject R C D M Y Z f
local notation "post" => dgGluingKernelConeRepresentativePost R C D M Y Z f p q KY

omit p q in
/-- 元の指定 kernel cochain を、その単位の 1 で評価した同じ次数 −1 元。 -/
def dgGluingKernelConeNullElement :
    (dgFunctorCommaHomComplex R (RightModule R D) (RightModule R C)
      (Morita.kernelTensor R D C M) KY L).X (-1) :=
  dgGluingUnitCochainElement _ (dgGluingKernelConeNullCochain R C D M Y Z f)

/-- 同じ代表射の実後合成で移した kernel 境界元。 -/
def dgGluingKernelConeRepresentativeNullElement :
    (dgFunctorCommaHomComplex R (RightModule R D) (RightModule R C)
      (Morita.kernelTensor R D C M) KY (dgGluingKernelObject R C D M W)).X (-1) :=
  (post).f (-1) (dgGluingKernelConeNullElement R C D M Y Z f)

/-- native 境界元の kernel 像は、指定した同じ kernel 元の実代表射による像。 -/
lemma dgGluingConeNullElement_kernel :
    (dgGluingKernelHomIso R C D M Y W).hom.f (-1)
      (dgGluingConeNullElement R C D M Y Z f p q) =
    dgGluingKernelConeRepresentativeNullElement R C D M Y Z f p q :=
  dgGluingUnitCochainElement_iso (dgGluingKernelConeNullCochain R C D M Y Z f)
    post (dgGluingKernelHomIso R C D M Y W)

/-- 指定 native 境界元の後合成も、同じ kernel 元による後合成へ厳密に移る。 -/
lemma dgGluingConeNullPost_kernel (X : G) :
    ((dgGluingGradedPostcomposition R G X Y W).f (-1)
      (dgGluingConeNullElement R C D M Y Z f p q)).comp
      (Cochain.ofHom (dgGluingKernelHomIso R C D M X W).hom) (add_zero (-1)) =
    (Cochain.ofHom (dgGluingKernelHomIso R C D M X Y).hom).comp
      ((dgGluingGradedPostcomposition R E ((dgGluingToKernelComma R C D M).obj X)
        ((dgGluingToKernelComma R C D M).obj Y) ((dgGluingToKernelComma R C D M).obj W)).f (-1)
        (dgGluingKernelConeRepresentativeNullElement R C D M Y Z f p q)) (zero_add (-1)) := by
  have he := dgGluingGradedPostcomposition_naturality R G E
    (dgGluingToKernelComma R C D M) X Y W (dgGluingConeNullElement R C D M Y Z f p q)
  rw [dgGluingToKernelComma_map, dgGluingToKernelComma_map, dgGluingToKernelComma_map] at he
  erw [dgGluingConeNullElement_kernel R C D M Y Z f p q] at he
  exact he

end SerrePositivity.InfinityCategories
