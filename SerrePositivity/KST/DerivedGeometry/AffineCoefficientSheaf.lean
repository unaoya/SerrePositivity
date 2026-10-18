module

public import SerrePositivity.KST.DerivedGeometry.AffineCoefficientComparison
public import SerrePositivity.KST.DerivedGeometry.AffineTensorSheaf
public import SerrePositivity.KST.DerivedGeometry.TensorCoefficientSheaf
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import SerrePositivity.KST.DerivedGeometry.ForgetSheafification

/-!
# アフィン係数環層の基礎加法群と tilde

概要：Spec R 上の具体的係数環層の基礎加法群を tilde H と同定する。
方針：環と加群から加法群への忘却が層化と可換であることを使う。
規約：H は非可換でもよく、平坦性も要求しない。
使われ方：KST D4・T1′、Bondal–van den Bergh Thm 3.1.1、Toën §3.2 のアフィン模型。
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
概要：環から加法群への忘却はアフィン上の層化の同値を保つ。
方針：基礎集合への忘却の一致を使う。
規約：非可換環を含む。
使われ方：KST D4、Toën §3.2 の係数環層の加法的比較。
-/
instance affineRingForget_preservesSheafification :
    (Opens.grothendieckTopology (Spec R)).PreservesSheafification
      (forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
  preservesSheafification_of_forget (forget₂ RingCat AddCommGrpCat) rfl

/--
概要：加群から加法群への忘却はアフィン上の層化の同値を保つ。
方針：基礎集合への忘却の一致を使う。
規約：任意の R 加群を扱う。
使われ方：KST D4、Toën §3.2 の tilde の加法的比較。
-/
instance affineModuleForget_preservesSheafification :
    (Opens.grothendieckTopology (Spec R)).PreservesSheafification
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) :=
  preservesSheafification_of_forget (forget₂ (ModuleCat R) AddCommGrpCat) rfl

/--
概要：アフィン係数環層の基礎加法群の層は tilde H の基礎加法群の層と自然同型。
方針：忘却と層化の可換性、加法的な前層比較、tilde の層化表示を合成する。
規約：環構造と構造層の作用の両立は後の比較で明示する。
使われ方：KST D4、Toën §3.2 の係数環層のアフィン切断の計算。
-/
def affineCoefficientSheafAdditiveIso :
    (sheafCompose (Opens.grothendieckTopology (Spec R))
      (forget₂ RingCat AddCommGrpCat)).obj
        (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).ring ≅
    (sheafCompose (Opens.grothendieckTopology (Spec R))
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat)).obj
        (modulesSpecToSheaf.obj (tilde (ModuleCat.of R H))) :=
  ((sheafComposeNatIso (Opens.grothendieckTopology (Spec R))
      (forget₂ RingCat AddCommGrpCat)
      (sheafificationAdjunction _ RingCat.{u})
      (sheafificationAdjunction _ AddCommGrpCat.{u})).app
        (coefficientTensorPresheaf H (Scheme.ΓSpecIso R).inv.hom)).symm ≪≫
    (presheafToSheaf (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u}).mapIso
      (affineCoefficientAdditiveIso H) ≪≫
    (sheafComposeNatIso (Opens.grothendieckTopology (Spec R))
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat)
      (sheafificationAdjunction _ (ModuleCat.{u} R))
      (sheafificationAdjunction _ AddCommGrpCat.{u})).app
        (affineModuleTensorPresheaf (ModuleCat.of R H)) ≪≫
    (sheafCompose (Opens.grothendieckTopology (Spec R))
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat)).mapIso
        (affineTensorSheafIso (ModuleCat.of R H))

/--
概要：係数環層の加法的な同型は、層化前のテンソルからの指定された比較と可換。
方針：忘却と層化の同型の単位との両立、単位の自然性、tilde の比較式を使う。
規約：後から任意の加法的同型を選ぶのではなく、構成した比較射との両立を示す。
使われ方：KST D4、Toën §3.2 のアフィン切断の環構造の比較。
-/
lemma affineCoefficientSheafAdditiveIso_fac :
    Functor.whiskerRight (tensorCoefficientComparison H (Scheme.ΓSpecIso R).inv.hom)
        (forget₂ RingCat AddCommGrpCat) ≫
      (affineCoefficientSheafAdditiveIso H).hom.hom =
    (affineCoefficientAdditiveIso H).hom ≫
      Functor.whiskerRight (affineTensorToTilde (ModuleCat.of R H))
        (forget₂ (ModuleCat.{u} R) AddCommGrpCat) := by
  change Functor.whiskerRight (toSheafify _ _) _ ≫
    (sheafifyComposeIso (Opens.grothendieckTopology (Spec R))
      (forget₂ RingCat AddCommGrpCat)
      (coefficientTensorPresheaf H (Scheme.ΓSpecIso R).inv.hom)).inv ≫
    sheafifyMap _ (affineCoefficientAdditiveIso H).hom ≫
    (sheafifyComposeIso (Opens.grothendieckTopology (Spec R))
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat)
      (affineModuleTensorPresheaf (ModuleCat.of R H))).hom ≫
    Functor.whiskerRight (affineTensorSheafIso (ModuleCat.of R H)).hom.hom _ = _
  rw [sheafComposeIso_inv_fac_assoc, ← toSheafify_naturality_assoc,
    sheafComposeIso_hom_fac_assoc]
  rw [← Functor.whiskerRight_comp, toSheafify_affineTensorSheafIso]

end SerrePositivity.KST.DerivedGeometry
