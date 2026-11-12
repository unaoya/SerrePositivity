module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
概要：有限個の加群の積と局所化を、分数を保つ線形同型で比較する。
方針：局所化を局所化環とのテンソル積に移し、Mathlib の有限積との交換を使う。
規約：有限積だけを扱う。分母に非零因子性は仮定しない。
使われ方：アフィン標準被覆の各 Čech 次数を局所化して完全性を検証する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (S : Submonoid R)
variable {I : Type} [Fintype I] [DecidableEq I]
variable (V : I → Type u) [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]

/-- 有限積と局所化の線形同型。 -/
def cechLocalizationPiEquiv :
    LocalizedModule S (∀ i, V i) ≃ₗ[R] (∀ i, LocalizedModule S (V i)) := by
  let e : LocalizedModule S (∀ i, V i) ≃ₗ[Localization S] (∀ i, LocalizedModule S (V i)) :=
    (LocalizedModule.equivTensorProduct S (∀ i, V i)).trans
      ((TensorProduct.piRight R (Localization S) (Localization S) V).trans
        (LinearEquiv.piCongrRight (fun i ↦ (LocalizedModule.equivTensorProduct S (V i)).symm)))
  exact e.restrictScalars R

/-- 有限積との比較は、すべての成分で同じ分母を保つ。 -/
theorem cechLocalizationPiEquiv_mk (x : ∀ i, V i) (s : S) (i : I) :
    cechLocalizationPiEquiv S V (LocalizedModule.mk x s) i = LocalizedModule.mk (x i) s := by
  change (LocalizedModule.equivTensorProduct S (V i)).symm
    ((TensorProduct.piRight R (Localization S) (Localization S) V
      (LocalizedModule.equivTensorProduct S (∀ i, V i) (LocalizedModule.mk x s))) i) = _
  rw [LocalizedModule.equivTensorProduct_apply_mk, TensorProduct.piRight_apply,
    TensorProduct.piRightHom_tmul, LocalizedModule.equivTensorProduct_symm_apply_tmul, one_smul]

/-- 有限積との比較の各成分は、射影を局所化した写像である。 -/
theorem cechLocalizationPiEquiv_projection (z : LocalizedModule S (∀ i, V i)) (i : I) :
    cechLocalizationPiEquiv S V z i =
      IsLocalizedModule.map S (LocalizedModule.mkLinearMap S (∀ i, V i))
        (LocalizedModule.mkLinearMap S (V i)) (LinearMap.proj i) z := by
  induction z using LocalizedModule.induction_on with
  | _ x s =>
    rw [cechLocalizationPiEquiv_mk, IsLocalizedModule.map_LocalizedModules,
      LinearMap.proj_apply]

end SerrePositivity.AlgebraicGeometry
