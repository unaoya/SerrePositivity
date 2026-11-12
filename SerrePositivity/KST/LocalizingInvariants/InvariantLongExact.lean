module

public import SerrePositivity.KST.LocalizingInvariants.InvariantPiComparison

/-!
概要：任意の抽象 Verdier 列に対する局所化不変量の値の整数 π 長完全列。
方針：像の実 fiber 四角形の長完全列を、元の値の群と元の包含・商の作用へ移す。
規約：Sp の安定性・追加の fiber 性の入力を要求しない。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant

variable {E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Sp.{u}} (hE : IsLocalizingInvariant E)
  (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.VerdierSequence.{u})
include hE

def leftGroupEquiv (j : ℤ) : NativeFiber.group (hE.abstractFiberTriangle d) 0 0 j ≃*
    valueHomotopyGroup E d.left j := (hE.fiberLeftGroupIso d j).commGroupIsoToMulEquiv

def middleGroupEquiv (j : ℤ) : NativeFiber.group (hE.abstractFiberTriangle d) 1 0 j ≃*
    valueHomotopyGroup E d.middle j := (hE.fiberMiddleGroupIso d j).commGroupIsoToMulEquiv

def rightGroupEquiv (j : ℤ) : NativeFiber.group (hE.abstractFiberTriangle d) 1 1 j ≃*
    valueHomotopyGroup E d.right j := (hE.fiberRightGroupIso d j).commGroupIsoToMulEquiv

lemma inclusion_equiv (j : ℤ) (a : NativeFiber.group (hE.abstractFiberTriangle d) 0 0 j) :
    hE.middleGroupEquiv d j (NativeFiber.bottom (hE.abstractFiberTriangle d) j a) =
      valueHomotopyMap E d.inclusion j (hE.leftGroupEquiv d j a) :=
  ConcreteCategory.congr_hom (hE.fiber_bottom_group_naturality d j) a

lemma projection_equiv (j : ℤ) (a : NativeFiber.group (hE.abstractFiberTriangle d) 1 0 j) :
    hE.rightGroupEquiv d j (NativeFiber.right (hE.abstractFiberTriangle d) j a) =
      valueHomotopyMap E d.projection j (hE.middleGroupEquiv d j a) :=
  ConcreteCategory.congr_hom (hE.fiber_right_group_naturality d j) a

/-- 元の値の群と包含・商の準同型に適合する接続準同型。 -/
def connecting (j : ℤ) : valueHomotopyGroup E d.right (j + 1) →*
    valueHomotopyGroup E d.left j :=
  (hE.leftGroupEquiv d j).toMonoidHom.comp
    ((NativeFiber.boundary (hE.abstractFiberTriangle d) (hE.abstractFiberTriangle_isFiber d) j).comp
      (hE.rightGroupEquiv d (j + 1)).symm.toMonoidHom)

lemma inclusion_inverse (j : ℤ) (a : valueHomotopyGroup E d.left j) :
    (hE.middleGroupEquiv d j).symm (valueHomotopyMap E d.inclusion j a) =
      NativeFiber.bottom (hE.abstractFiberTriangle d) j ((hE.leftGroupEquiv d j).symm a) := by
  apply (hE.middleGroupEquiv d j).injective
  rw [MulEquiv.apply_symm_apply, hE.inclusion_equiv, MulEquiv.apply_symm_apply]

lemma projection_inverse (j : ℤ) (a : valueHomotopyGroup E d.middle j) :
    (hE.rightGroupEquiv d j).symm (valueHomotopyMap E d.projection j a) =
      NativeFiber.right (hE.abstractFiberTriangle d) j ((hE.middleGroupEquiv d j).symm a) := by
  apply (hE.rightGroupEquiv d j).injective
  rw [MulEquiv.apply_symm_apply, hE.projection_equiv, MulEquiv.apply_symm_apply]

lemma connecting_inverse (j : ℤ) (a : valueHomotopyGroup E d.right (j + 1)) :
    (hE.leftGroupEquiv d j).symm (hE.connecting d j a) =
      NativeFiber.boundary (hE.abstractFiberTriangle d) (hE.abstractFiberTriangle_isFiber d) j
        ((hE.rightGroupEquiv d (j + 1)).symm a) :=
  (hE.leftGroupEquiv d j).symm_apply_apply _

lemma exact_left (j : ℤ) (a : valueHomotopyGroup E d.left j) :
    valueHomotopyMap E d.inclusion j a = 1 ↔
      ∃ b : valueHomotopyGroup E d.right (j + 1), hE.connecting d j b = a :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.group_exact_of_equivalences (hE.connecting d j) (valueHomotopyMap E d.inclusion j)
    (NativeFiber.boundary (hE.abstractFiberTriangle d) (hE.abstractFiberTriangle_isFiber d) j)
    (NativeFiber.bottom (hE.abstractFiberTriangle d) j)
    (hE.rightGroupEquiv d (j + 1)).symm (hE.leftGroupEquiv d j).symm
    (hE.middleGroupEquiv d j).symm (hE.connecting_inverse d j) (hE.inclusion_inverse d j)
    (NativeFiber.exact_fiber (hE.abstractFiberTriangle d) (hE.abstractFiberTriangle_isFiber d) j) a

lemma exact_middle (j : ℤ) (a : valueHomotopyGroup E d.middle j) :
    valueHomotopyMap E d.projection j a = 1 ↔
      ∃ b : valueHomotopyGroup E d.left j, valueHomotopyMap E d.inclusion j b = a :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.group_exact_of_equivalences (valueHomotopyMap E d.inclusion j)
    (valueHomotopyMap E d.projection j)
    (NativeFiber.bottom (hE.abstractFiberTriangle d) j)
    (NativeFiber.right (hE.abstractFiberTriangle d) j)
    (hE.leftGroupEquiv d j).symm (hE.middleGroupEquiv d j).symm (hE.rightGroupEquiv d j).symm
    (hE.inclusion_inverse d j) (hE.projection_inverse d j)
    (NativeFiber.exact_total (hE.abstractFiberTriangle d) (hE.abstractFiberTriangle_isFiber d) j) a

lemma exact_right (j : ℤ) (a : valueHomotopyGroup E d.right (j + 1)) :
    hE.connecting d j a = 1 ↔ ∃ b : valueHomotopyGroup E d.middle (j + 1),
      valueHomotopyMap E d.projection (j + 1) b = a :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.group_exact_of_equivalences (valueHomotopyMap E d.projection (j + 1)) (hE.connecting d j)
    (NativeFiber.right (hE.abstractFiberTriangle d) (j + 1))
    (NativeFiber.boundary (hE.abstractFiberTriangle d) (hE.abstractFiberTriangle_isFiber d) j)
    (hE.middleGroupEquiv d (j + 1)).symm (hE.rightGroupEquiv d (j + 1)).symm
    (hE.leftGroupEquiv d j).symm (hE.projection_inverse d (j + 1)) (hE.connecting_inverse d j)
    (NativeFiber.exact_base (hE.abstractFiberTriangle d) (hE.abstractFiberTriangle_isFiber d) j) a

end SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
