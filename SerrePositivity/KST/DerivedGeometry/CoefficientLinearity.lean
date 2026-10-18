module

public import SerrePositivity.KST.DerivedGeometry.CoefficientConstantAction
public import SerrePositivity.KST.DerivedGeometry.CoefficientForget
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

/-!
概要：構造層上の射の係数線形性を定数係数の作用との可換性から再構成する。
方針：純テンソルを二つの因子の積で表し、テンソル帰納と層化の局所全射性を使う。
規約：H の可換性・平坦性は仮定しない。
使われ方：KST D4・T1′、Toën §3.2 のアフィン係数加群圏の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct
namespace SerrePositivity.KST.DerivedGeometry
variable {A : Type u} [CommRing A] (H : Type u) [Ring H] [Algebra A H]
  {X : Scheme.{u}} (a : A →+* Γ(X, ⊤))

/--
概要：層化した純テンソルは定数係数の切断と構造層の切断の積。
方針：層化前の純テンソルの積を計算して比較の環準同型で送る。
規約：積の順序は H の因子が先。
使われ方：KST D4・T1′、Toën §3.2 の係数線形性の判定。
-/
theorem tensorCoefficientComparison_tmul (U : X.Opens) (h : H) (r : Γ(X, U)) :
    letI : Algebra A Γ(X, U) := sectionAlgebra a U
    (tensorCoefficientComparison H a).app (.op U) (h ⊗ₜ[A] r) =
      (tensorCoefficientConstant H a).app (.op U) h *
        (tensorCoefficientSheaf H a).structureMap.hom.app (.op U) r := by
  let : Algebra A Γ(X, U) := sectionAlgebra a U
  change ((tensorCoefficientComparison H a).app (.op U)).hom (h ⊗ₜ[A] r) =
    ((tensorCoefficientComparison H a).app (.op U)).hom (h ⊗ₜ[A] (1 : Γ(X, U))) *
      ((tensorCoefficientComparison H a).app (.op U)).hom ((1 : H) ⊗ₜ[A] r)
  rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/--
概要：定数作用と可換な O 線形射は、層化前の全テンソル係数に対して線形。
方針：純テンソルで二つの作用の両立を使い、テンソルの和で帰納する。
規約：任意の開集合と係数加群層で成立する。
使われ方：KST D4・T1′、Toën §3.2 の係数線形な射の再構成。
-/
theorem coefficientUnderlyingHom_tensor_smul
    {M N : (tensorCoefficientSheaf H a).Modules}
    (φ : (tensorCoefficientSheaf H a).forget.obj M ⟶
      (tensorCoefficientSheaf H a).forget.obj N)
    (hφ : ∀ h : H, coefficientConstantAction H a M h ≫ φ =
      φ ≫ coefficientConstantAction H a N h)
    (U : X.Opens) (t : (coefficientTensorPresheaf H a).obj (.op U)) (m : M.val.obj (.op U)) :
    (φ.val.app (.op U)).hom ((tensorCoefficientComparison H a).app (.op U) t • m) =
      (tensorCoefficientComparison H a).app (.op U) t •
        (show N.val.obj (.op U) from (φ.val.app (.op U)).hom m) := by
  let : Algebra A Γ(X, U) := sectionAlgebra a U
  change H ⊗[A] Γ(X, U) at t
  induction t using TensorProduct.inductionOn with
  | tmul h r =>
    rw [tensorCoefficientComparison_tmul, mul_smul, mul_smul]
    have hh := congrArg (fun f => (f.val.app (.op U)).hom
      ((tensorCoefficientSheaf H a).structureMap.hom.app (.op U) r • m)) (hφ h)
    change (φ.val.app (.op U)).hom
      ((tensorCoefficientConstant H a).app (.op U) h •
        ((tensorCoefficientSheaf H a).structureMap.hom.app (.op U) r • m)) =
      (tensorCoefficientConstant H a).app (.op U) h •
        (show N.val.obj (.op U) from (φ.val.app (.op U)).hom
          ((tensorCoefficientSheaf H a).structureMap.hom.app (.op U) r • m)) at hh
    exact hh.trans (congrArg (fun z : N.val.obj (.op U) =>
      (tensorCoefficientConstant H a).app (.op U) h • z)
      ((φ.val.app (.op U)).hom.map_smul r m))
  | add t s ht hs =>
    simp only [map_add, add_smul, ht, hs]

/--
概要：全定数係数作用と可換な O 加群層の射から係数加群層の射を再構成する。
方針：テンソル前層に対する線形性と層化比較の局所全射性を使う。
規約：定数切断だけで大域的な全射性を仮定しない。
使われ方：KST D4・T1′、Toën §3.2 のアフィン係数加群圏の充満性。
-/
def coefficientHomOfCommutes
    {M N : (tensorCoefficientSheaf H a).Modules}
    (φ : (tensorCoefficientSheaf H a).forget.obj M ⟶
      (tensorCoefficientSheaf H a).forget.obj N)
    (hφ : ∀ h : H, coefficientConstantAction H a M h ≫ φ =
      φ ≫ coefficientConstantAction H a N h) : M ⟶ N :=
  ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective
    (tensorCoefficientComparison H a) N.isSheaf).symm
      (PresheafOfModules.homMk
        ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map φ.val)
        (fun U t m => coefficientUnderlyingHom_tensor_smul H a φ hφ U.unop t m))⟩

/--
概要：再構成した係数加群層の射は、係数を忘れると元の O 加群層の射。
方針：各開の切断上で、局所全射の Hom 同値の逆の具体的な式を読む。
規約：元の切断上の写像は変更しない。
使われ方：KST D4・T1′、Toën §3.2 の再構成の正確性。
-/
theorem coefficientHomOfCommutes_forget
    {M N : (tensorCoefficientSheaf H a).Modules}
    (φ : (tensorCoefficientSheaf H a).forget.obj M ⟶
      (tensorCoefficientSheaf H a).forget.obj N)
    (hφ : ∀ h : H, coefficientConstantAction H a M h ≫ φ =
      φ ≫ coefficientConstantAction H a N h) :
    (tensorCoefficientSheaf H a).forget.map (coefficientHomOfCommutes H a φ hφ) = φ := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  rfl

/--
概要：係数加群層の射を O 加群層へ忘れると全ての定数係数作用と可換。
方針：各開で係数環層上の線形性を定数切断へ適用する。
規約：非可換 H に対する左加群の順序を保持する。
使われ方：KST D4・T1′、Toën §3.2 の係数作用付き射の記述。
-/
theorem coefficientHom_commutesConstant
    {M N : (tensorCoefficientSheaf H a).Modules} (f : M ⟶ N) (h : H) :
    coefficientConstantAction H a M h ≫ (tensorCoefficientSheaf H a).forget.map f =
      (tensorCoefficientSheaf H a).forget.map f ≫ coefficientConstantAction H a N h := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change M.val.obj U at m
  change (f.val.app U).hom ((tensorCoefficientConstant H a).app U h • m) =
    (tensorCoefficientConstant H a).app U h • (f.val.app U).hom m
  exact (f.val.app U).hom.map_smul _ _

/--
概要：係数加群層の射は全定数係数作用と可換な O 加群層の射と同値。
方針：層化の局所全射性から作った逆と係数忘却の忠実性を使う。
規約：平坦性・可換性・準連接性を仮定しない。
使われ方：KST D4・T1′、Toën §3.2 のアフィン係数加群圏の比較。
-/
def coefficientHomEquiv (M N : (tensorCoefficientSheaf H a).Modules) :
    (M ⟶ N) ≃ {φ : (tensorCoefficientSheaf H a).forget.obj M ⟶
        (tensorCoefficientSheaf H a).forget.obj N //
      ∀ h : H, coefficientConstantAction H a M h ≫ φ =
        φ ≫ coefficientConstantAction H a N h} where
  toFun f := ⟨(tensorCoefficientSheaf H a).forget.map f, coefficientHom_commutesConstant H a f⟩
  invFun φ := coefficientHomOfCommutes H a φ.val φ.property
  left_inv f := by
    apply (tensorCoefficientSheaf H a).forget.map_injective
    exact coefficientHomOfCommutes_forget H a _ _
  right_inv φ := Subtype.ext (coefficientHomOfCommutes_forget H a _ _)

end SerrePositivity.KST.DerivedGeometry
