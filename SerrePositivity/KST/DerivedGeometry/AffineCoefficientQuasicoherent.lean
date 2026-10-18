module

public import SerrePositivity.KST.DerivedGeometry.AffineCoefficientModule

/-!
# アフィン係数環層の準連接性

概要：係数環層の正則 O 加群を tilde H と同定し、準連接性を得る。
方針：指定した環層化の比較と O 加群射の可換性を基本開上で使う。
規約：平坦性は仮定しない。一般の底変換と導来生成は別定理。
使われ方：KST D4・T1、Bondal–van den Bergh Thm 3.1.1、Toën §3.2。
-/

@[expose] public section

noncomputable section

set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace SerrePositivity.KST.DerivedGeometry

variable {R : CommRingCat.{u}} (H : Type u) [Ring H] [Algebra R H]

/--
概要：O 加群の比較は指定された環層化の比較と可換。
方針：加法的テンソルからの射を純テンソルで判定する。
規約：環前層と加群前層のスカラーの同一視も式に含める。
使われ方：KST D4、Toën §3.2 の基本開上での同型の移送。
-/
lemma affineCoefficientModuleMap_fac (U : (Spec R).Opens) :
    (affineCoefficientAdditiveIso H).hom.app (.op U) ≫
      (forget₂ (ModuleCat R) AddCommGrpCat).map
        ((affineTensorToTilde (ModuleCat.of R H)).app (.op U)) ≫
      (forget₂ (ModuleCat R) AddCommGrpCat).map
        ((modulesSpecToSheaf.map (affineCoefficientModuleMap H)).hom.app (.op U)) =
    (forget₂ RingCat AddCommGrpCat).map
      ((tensorCoefficientComparison H (Scheme.ΓSpecIso R).inv.hom).app (.op U)) := by
  apply affineTensorAdditiveObject_hom_ext H U
    (sectionAlgebra (Scheme.ΓSpecIso R).inv.hom U)
  intro h s
  change ((modulesSpecToSheaf.map (affineCoefficientModuleMap H)).hom.app (.op U))
    (((affineTensorToTilde (ModuleCat.of R H)).app (.op U))
      ((affineCoefficientAdditiveIsoAt H U).hom
        (affineTensorAdditivePure H U
          (sectionAlgebra (Scheme.ΓSpecIso R).inv.hom U) h s))) = _
  erw [affineCoefficientAdditiveIsoAt_pure]
  exact affineCoefficientModuleMap_tmul H U h s

/--
概要：正則 O 加群への比較は各基本開の切断で同型。
方針：可換式の他の三射が同型であることから加法的な同型を得る。
規約：R 加群に忘れた切断上の射を判定する。
使われ方：KST D4、Toën §3.2 の開基による層の同型判定。
-/
instance affineCoefficientModuleMap_basic_isIso (f : R) :
    IsIso ((modulesSpecToSheaf.map (affineCoefficientModuleMap H)).hom.app
      (.op (PrimeSpectrum.basicOpen f))) := by
  let U := PrimeSpectrum.basicOpen f
  let γ := (affineCoefficientAdditiveIso H).hom.app (.op U)
  let α := (forget₂ (ModuleCat R) AddCommGrpCat).map
    ((affineTensorToTilde (ModuleCat.of R H)).app (.op U))
  let δ := (forget₂ (ModuleCat R) AddCommGrpCat).map
    ((modulesSpecToSheaf.map (affineCoefficientModuleMap H)).hom.app (.op U))
  have : IsIso γ := by dsimp [γ]; infer_instance
  have : IsIso α := by
    change IsIso ((forget₂ (ModuleCat R) AddCommGrpCat).map
      ((affineTensorToTilde (ModuleCat.of R H)).app (.op (PrimeSpectrum.basicOpen f))))
    infer_instance
  have : IsIso (γ ≫ α ≫ δ) := by
    rw [affineCoefficientModuleMap_fac H U]
    dsimp [U]
    infer_instance
  have : IsIso (α ≫ δ) := (isIso_comp_left_iff γ _).mp inferInstance
  have : IsIso δ := (isIso_comp_left_iff α δ).mp inferInstance
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact ConcreteCategory.bijective_of_isIso δ

/--
概要：tilde H から係数環層の正則 O 加群への比較は同型。
方針：基本開上の切断の同型と、構造層加群から R 加群層への忠実充満な忘却を使う。
規約：標準構造射 Spec R 上での同型。
使われ方：KST D4、Toën §3.2 のアフィン準連接性。
-/
instance affineCoefficientModuleMap_isIso :
    IsIso (affineCoefficientModuleMap (R := R) H) := by
  have : IsIso (modulesSpecToSheaf.map (affineCoefficientModuleMap (R := R) H)) :=
    TopCat.Sheaf.isIso_iff_isIso_basis PrimeSpectrum.isBasis_basic_opens
      (fun f => affineCoefficientModuleMap_basic_isIso H f)
  exact isIso_of_reflects_iso (affineCoefficientModuleMap (R := R) H) modulesSpecToSheaf

/--
概要：係数環層の正則 O 加群は tilde H と標準的に同型。
方針：証明済みの比較射の同型性を束ねる。
規約：環の可換性や平坦性は不要。
使われ方：KST D4・T1、Toën §3.2 の係数環層の局所模型。
-/
def affineCoefficientModuleIso : tilde (ModuleCat.of R H) ≅
    (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).regular :=
  asIso (affineCoefficientModuleMap H)

/--
概要：アフィン係数環層の正則 O 加群は準連接。
方針：tilde H の準連接性を構成した O 加群層の同型で移送する。
規約：T1 のコンパクト生成や導来随伴はこの主張に含めない。
使われ方：KST D4・T1、Bondal–van den Bergh Thm 3.1.1、Toën §3.2。
-/
instance affineCoefficientRegular_isQuasicoherent :
    (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).regular.IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    (affineCoefficientModuleIso H) inferInstance

end SerrePositivity.KST.DerivedGeometry
