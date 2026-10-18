module

public import SerrePositivity.KST.DerivedGeometry.CoefficientActionPresheaf
public import SerrePositivity.KST.DerivedGeometry.TensorCoefficientAction
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafify

/-!
概要：基礎環と両立する H 作用を持つ O 加群層を実際の係数環層上の加群層へする。
方針：テンソル係数前層を層化比較に沿って層化し、元の加法群の層を保持する。
規約：H の平坦性・可換性を仮定しない。
使われ方：KST D4・T1′、Toën §3.2 のアフィン係数加群圏の本質的全射性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace SerrePositivity.KST.DerivedGeometry
variable {A : Type u} [CommRing A] (H : Type u) [Ring H] [Algebra A H]
  {X : Scheme.{u}} (a : A →+* Γ(X, ⊤))

/--
概要：テンソル前層から係数環層への比較は局所単射。
方針：実際の層化の単位の局所単射性を使う。
規約：大域切断上の単射性は要求しない。
使われ方：KST D4、Toën §3.2 の係数作用の層化。
-/
instance tensorCoefficientComparison_locallyInjective :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (tensorCoefficientComparison H a) := by
  change Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
    (toSheafify (Opens.grothendieckTopology X) (coefficientTensorPresheaf H a))
  infer_instance

/--
概要：基礎環上で両立する H 作用から係数環層上の加群層を構成する。
方針：テンソル係数前層の基礎加法群をそのまま層として用い、局所全単射な係数比較で作用を拡張する。
規約：元の O 加群層の加法群と切断の制限を変更しない。
使われ方：KST D4・T1′、Toën §3.2 の係数 tilde 層。
-/
def coefficientModuleOfAction (M : X.Modules) (ρ : H →+* End M)
    (hρ : ∀ r : A, (ρ (algebraMap A H r)).asHom = structureScalarAction a M r) :
    (tensorCoefficientSheaf H a).Modules :=
  PresheafOfModules.sheafify
    (M₀ := coefficientActionPresheaf H a M ρ hρ)
    (A := ⟨M.val.presheaf, M.isSheaf⟩)
    (tensorCoefficientComparison H a) (𝟙 _)

/--
概要：層化前の係数の像の作用は元のテンソル作用に一致する。
方針：加群の層化の単位の線形性と、基礎加法群上での恒等性を使う。
規約：比較の像に対する作用を同じ切断上で計算する。
使われ方：KST D4・T1′、Toën §3.2 の基礎環と H 作用の復元。
-/
theorem coefficientModuleOfAction_comparison_smul (M : X.Modules) (ρ : H →+* End M)
    (hρ : ∀ r : A, (ρ (algebraMap A H r)).asHom = structureScalarAction a M r)
    (U : X.Opens) (t : (coefficientTensorPresheaf H a).obj (.op U)) (m : M.val.obj (.op U)) :
    (tensorCoefficientComparison H a).app (.op U) t •
        (show (coefficientModuleOfAction H a M ρ hρ).val.obj (.op U) from m) =
      (show (coefficientModuleOfAction H a M ρ hρ).val.obj (.op U) from
        coefficientTensorSectionEnd H a M ρ hρ U t m) := by
  let g := PresheafOfModules.toSheafify
    (M₀ := coefficientActionPresheaf H a M ρ hρ)
    (A := ⟨M.val.presheaf, M.isSheaf⟩)
    (tensorCoefficientComparison H a) (𝟙 _)
  exact ((g.app (.op U)).hom.map_smul t m).symm

/--
概要：再構成した係数加群層の構造層スカラー作用は元のもの。
方針：右因子の純テンソルの作用と H の単位の作用を計算する。
規約：基礎 O 加群の比較には同じ切断の恒等写像を使う。
使われ方：KST D4・T1′、Toën §3.2 の基礎層の復元。
-/
theorem coefficientModuleOfAction_structure_smul (M : X.Modules) (ρ : H →+* End M)
    (hρ : ∀ r : A, (ρ (algebraMap A H r)).asHom = structureScalarAction a M r)
    (U : X.Opens) (r : Γ(X, U)) (m : M.val.obj (.op U)) :
    (tensorCoefficientSheaf H a).structureMap.hom.app (.op U) r •
        (show (coefficientModuleOfAction H a M ρ hρ).val.obj (.op U) from m) =
      (show (coefficientModuleOfAction H a M ρ hρ).val.obj (.op U) from r • m) := by
  let := sectionAlgebra a U
  let := structureSectionModule M U
  have hc := coefficientModuleOfAction_comparison_smul H a M ρ hρ U
    ((coefficientTensorUnit H a).app (.op U) r) m
  have ht := coefficientTensorSectionEnd_tmul_apply H a M ρ hρ U (1 : H) r m
  have ho : ((ρ 1).asHom.val.app (.op U)).hom m = m :=
    congrArg (fun f : End M => (f.asHom.val.app (.op U)).hom m) ρ.map_one
  exact hc.trans (ht.trans (congrArg (fun z : M.val.obj (.op U) => r • z) ho))

/--
概要：再構成した係数加群層の定数 H 作用は元の H 作用。
方針：左因子の純テンソルの作用と局所スカラーの単位を計算する。
規約：H の各作用射を元のものとして保持する。
使われ方：KST D4・T1′、Toën §3.2 の大域切断の H 線形性。
-/
theorem coefficientModuleOfAction_constant_smul (M : X.Modules) (ρ : H →+* End M)
    (hρ : ∀ r : A, (ρ (algebraMap A H r)).asHom = structureScalarAction a M r)
    (U : X.Opens) (h : H) (m : M.val.obj (.op U)) :
    (tensorCoefficientConstant H a).app (.op U) h •
        (show (coefficientModuleOfAction H a M ρ hρ).val.obj (.op U) from m) =
      (show (coefficientModuleOfAction H a M ρ hρ).val.obj (.op U) from
        ((ρ h).asHom.val.app (.op U)).hom m) := by
  let := sectionAlgebra a U
  let := structureSectionModule M U
  exact (coefficientModuleOfAction_comparison_smul H a M ρ hρ U
    ((coefficientTensorConstant H a).app (.op U) h) m).trans
      ((coefficientTensorSectionEnd_tmul_apply H a M ρ hρ U h 1 m).trans (one_smul _ _))

/--
概要：H 作用から再構成した係数加群層を O へ忘れると元の O 加群層と同型。
方針：同じ加法群の各切断上の恒等同型に、証明済みのスカラー作用の一致を添える。
規約：同型の基礎写像は全ての開で恒等。
使われ方：KST D4・T1′、Toën §3.2 の準連接性の保存。
-/
def coefficientModuleOfActionForgetIso (M : X.Modules) (ρ : H →+* End M)
    (hρ : ∀ r : A, (ρ (algebraMap A H r)).asHom = structureScalarAction a M r) :
    (tensorCoefficientSheaf H a).forget.obj (coefficientModuleOfAction H a M ρ hρ) ≅ M := by
  let e : ((tensorCoefficientSheaf H a).forget.obj
      (coefficientModuleOfAction H a M ρ hρ)).val ≅ M.val :=
    PresheafOfModules.isoMk (fun U => ModuleCat.isoMk (Iso.refl _) (by
      intro r
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro m
      exact (coefficientModuleOfAction_structure_smul H a M ρ hρ U.unop r m).symm))
      (by intro U V i; ext m; rfl)
  exact (SheafOfModules.fullyFaithfulForget X.ringCatSheaf).preimageIso e

end SerrePositivity.KST.DerivedGeometry
