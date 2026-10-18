module

public import SerrePositivity.KST.DerivedGeometry.BaseSections
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# アフィン上のテンソルと tilde の基本開切断

概要：基本開上の tilde の切断を、構造層の切断とのテンソル積で表す。
方針：tilde の基本開切断の加群局所化を、局所化環による底変換に直す。
規約：加群の平坦性・有限生成性は要求しない。
使われ方：KST D4・T1′、Bondal–van den Bergh Thm 3.1.1、Toën §3.2 のアフィン模型。
-/

@[expose] public section

noncomputable section

set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

namespace SerrePositivity.KST.DerivedGeometry

/--
概要：Spec R の標準的な基礎環写像を制限すると既存の切断の代数構造を得る。
方針：大域切断の標準同型と制限写像の定義を展開する。
規約：R の任意の開についての等式。
使われ方：KST D4、Toën §3.2 の具体的テンソル前層と Mathlib のアフィン切断の接続。
-/
lemma sectionBaseMap_spec (R : CommRingCat.{u}) (U : (Spec R).Opens) :
    sectionBaseMap (Scheme.ΓSpecIso R).inv.hom U = algebraMap R Γ(Spec R, U) := rfl

/--
概要：明示的に構成した Spec R の切断の代数構造は Mathlib の標準構造と一致する。
方針：代数構造を基礎環の写像の一致で判定する。
規約：構造の一致を示し、型変換時のスカラー作用の曖昧さを除く。
使われ方：KST D4、Toën §3.2 のテンソル前層のアフィン計算。
-/
lemma sectionAlgebra_spec (R : CommRingCat.{u}) (U : (Spec R).Opens) :
    sectionAlgebra (Scheme.ΓSpecIso R).inv.hom U =
      (inferInstance : Algebra R Γ(Spec R, U)) :=
  Algebra.algebra_ext _ _ (fun _ => rfl)

/--
概要：基本開 D(f) 上の tilde M の切断は M と O(D(f)) のテンソル積に線形同型。
方針：tilde の局所化の普遍性を底変換の普遍性に直し、テンソルの因子を交換する。
規約：M は任意の R 加群であり、平坦性や有限性を仮定しない。
使われ方：KST D4・T1′、Bondal–van den Bergh Thm 3.1.1 のアフィン段階、Toën §3.2。
-/
def affineBasicTensorSectionsEquiv {R : CommRingCat.{u}} (M : ModuleCat.{u} R) (f : R) :
    M ⊗[R] Γ(Spec R, PrimeSpectrum.basicOpen f) ≃ₗ[R]
      Γ(tilde M, PrimeSpectrum.basicOpen f) := by
  let g : M →ₗ[R] Γ(tilde M, PrimeSpectrum.basicOpen f) :=
    (tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom
  have : IsLocalizedModule (.powers f) g :=
    inferInstanceAs (IsLocalizedModule (.powers f)
      (tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom)
  exact (TensorProduct.comm R M Γ(Spec R, PrimeSpectrum.basicOpen f)).trans
    ((IsLocalizedModule.isBaseChange (.powers f) Γ(Spec R, PrimeSpectrum.basicOpen f)
      g).equiv.restrictScalars R)

/--
概要：基本開上のテンソル同型は m ⊗ s を s 倍した m の標準切断に送る。
方針：底変換の同型の純テンソルに対する計算を使う。
規約：右因子の構造層の作用を明示する。
使われ方：KST D4・T1′、Toën §3.2 の制限写像との自然性の計算。
-/
lemma affineBasicTensorSectionsEquiv_tmul {R : CommRingCat.{u}}
    (M : ModuleCat.{u} R) (f : R) (m : M) (s : Γ(Spec R, PrimeSpectrum.basicOpen f)) :
    affineBasicTensorSectionsEquiv M f (m ⊗ₜ[R] s) =
      s • (show Γ(tilde M, PrimeSpectrum.basicOpen f) from
        (tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom m) := by
  simp only [affineBasicTensorSectionsEquiv, LinearEquiv.trans_apply,
    TensorProduct.comm_tmul, LinearEquiv.restrictScalars_apply, IsBaseChange.equiv_tmul]
  rfl

end SerrePositivity.KST.DerivedGeometry
