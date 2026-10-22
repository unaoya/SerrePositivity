module
public import SerrePositivity.InfinityCategories.Derived.Gluing.KernelConeRepresentatives
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaPostHomotopyCriterion

/-! 選んだ円錐代表への実閉射は、任意試験対象からの全 Hom にホモトピー同値を誘導する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory HomologicalComplex CochainComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (Y Z : DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
  (p : DGGluingConeRepresentative R C Y.left Z.left (dgGluingConeLeftArrow R C D M Y Z f))
  (q : DGGluingConeRepresentative R D Y.right Z.right
    ((dgYoneda R D).onClosed.map (dgGluingConeRightArrow R C D M Y Z f)))
local notation "W" => dgGluingConeObjectFromRepresentatives R C D M Y Z f p q
local notation "L" => dgGluingKernelConeObject R C D M Y Z f
local notation "T" => dgGluingKernelObject R C D M W
local notation "a" => dgGluingKernelConeRepresentativeMap R C D M Y Z f p q
local notation "Qh" => _root_.HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)

/-- 選んだ円錐代表への同じ実閉射による、全 Hom の実後合成写像。 -/
def dgGluingKernelConeRepresentativePost
    (V : DGFunctorCommaObject R (RightModule R D) (RightModule R C)
      (Morita.kernelTensor R D C M)) :
    dgFunctorCommaHomComplex R (RightModule R D) (RightModule R C)
      (Morita.kernelTensor R D C M) V L ⟶
    dgFunctorCommaHomComplex R (RightModule R D) (RightModule R C)
      (Morita.kernelTensor R D C M) V T :=
  eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) V)
    (Y := ForgetEnrichment.of (Complex R) L) (Y' := ForgetEnrichment.of (Complex R) T) a

variable (V : DGFunctorCommaObject R (RightModule R D) (RightModule R C)
      (Morita.kernelTensor R D C M))

/-- 円錐代表への同じ実閉射の全 Hom 後合成は、通常複体のホモトピー圏で同型。 -/
lemma dgGluingKernelConeRepresentativePost_isIso :
    IsIso ((Qh).map (dgGluingKernelConeRepresentativePost R C D M Y Z f p q V)) := by
  have hs : IsIso ((moduleToHomotopy R D).map
      ((dgFunctorCommaSource R (RightModule R D) (RightModule R C)
        (Morita.kernelTensor R D C M)).onClosed.map a)) := by
    rw [dgGluingKernelConeRepresentativeMap_source_homotopy R C D M Y Z f p q]
    infer_instance
  have ht : IsIso ((moduleToHomotopy R C).map
      ((dgFunctorCommaReplacement R (RightModule R D) (RightModule R C)
        (Morita.kernelTensor R D C M)).onClosed.map a)) := by
    rw [dgGluingKernelConeRepresentativeMap_replacement_homotopy R C D M Y Z f p q]
    infer_instance
  exact dgGluingCommaPostHomotopy_isIso R (RightModule R D) (RightModule R C)
    (Morita.kernelTensor R D C M) V L T a hs ht

/-- 同じ後合成写像自身に、実鎖写像のホモトピー逆と両ホモトピーが存在する。 -/
lemma dgGluingKernelConeRepresentativePost_equivalence :
    homotopyEquivalences (ModuleCat R) (ComplexShape.up ℤ)
      (dgGluingKernelConeRepresentativePost R C D M Y Z f p q V) :=
  (isIso_quotient_map_iff_homotopyEquivalences _).1
    (dgGluingKernelConeRepresentativePost_isIso R C D M Y Z f p q V)

/-- 元の後合成写像を順射に保つ、円錐代表への全 Hom のホモトピー同値。 -/
def dgGluingKernelConeRepresentativePostEquiv :
    HomotopyEquiv
      (dgFunctorCommaHomComplex R (RightModule R D) (RightModule R C)
        (Morita.kernelTensor R D C M) V L)
      (dgFunctorCommaHomComplex R (RightModule R D) (RightModule R C)
        (Morita.kernelTensor R D C M) V T) :=
  Classical.choose (dgGluingKernelConeRepresentativePost_equivalence R C D M Y Z f p q V)

/-- 選んだホモトピー同値の順射は、同じ実閉射による後合成そのもの。 -/
lemma dgGluingKernelConeRepresentativePostEquiv_hom :
    (dgGluingKernelConeRepresentativePostEquiv R C D M Y Z f p q V).hom =
      dgGluingKernelConeRepresentativePost R C D M Y Z f p q V :=
  Classical.choose_spec (dgGluingKernelConeRepresentativePost_equivalence R C D M Y Z f p q V)

variable (X : DGGluingObject R C D M)

/-- 元の gluing Hom 円錐を、選んだ円錐対象の kernel 表示への Hom にホモトピー同値で移す。 -/
def dgGluingHomConeKernelRepresentativeEquiv :
    HomotopyEquiv (mappingCone (dgGluingPostcomposition R C D M X Y Z f))
      (dgFunctorCommaHomComplex R (RightModule R D) (RightModule R C) (Morita.kernelTensor R D C M)
        (dgGluingKernelObject R C D M X) T) :=
  (HomotopyEquiv.ofIso (dgGluingHomConeKernelIso R C D M X Y Z f)).trans
    (dgGluingKernelConeRepresentativePostEquiv R C D M Y Z f p q
      (dgGluingKernelObject R C D M X))

/-- 合成したホモトピー同値も、標準 Hom 円錐比較と同じ実後合成を順射に保つ。 -/
lemma dgGluingHomConeKernelRepresentativeEquiv_hom :
    (dgGluingHomConeKernelRepresentativeEquiv R C D M Y Z f p q X).hom =
    (dgGluingHomConeKernelIso R C D M X Y Z f).hom ≫
      dgGluingKernelConeRepresentativePost R C D M Y Z f p q
        (dgGluingKernelObject R C D M X) := by
  change (dgGluingHomConeKernelIso R C D M X Y Z f).hom ≫
    (dgGluingKernelConeRepresentativePostEquiv R C D M Y Z f p q
      (dgGluingKernelObject R C D M X)).hom = _
  rw [dgGluingKernelConeRepresentativePostEquiv_hom]

end SerrePositivity.InfinityCategories
