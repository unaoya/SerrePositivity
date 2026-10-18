module

public import SerrePositivity.KST.DerivedGeometry.AffineBaseChangeSections
public import SerrePositivity.KST.DerivedGeometry.AffineCoefficientSections

/-!
# アフィン係数環層の底変換

概要：一般の A → R に対する係数環層を底変換後の R 係数環層と同定する。
方針：テンソル前層の自然同型を層化し、比較射の自然性を使う。
規約：H は非可換でもよく、A 上の平坦性も要求しない。
使われ方：KST D4、Toën Derived Azumaya §3.2 のアフィン模型。
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

variable (A : Type u) [CommRing A] (R : CommRingCat.{u}) [Algebra A R]
  (H : Type u) [Ring H] [Algebra A H]

/--
概要：係数を H ⊗_A R へ底変換して構成した環層と、A 係数で構成した環層は同型。
方針：指定したテンソル前層の自然同型を環の圏で層化する。
規約：H ⊗_A R の R 作用は右因子由来。
使われ方：KST D4、Toën §3.2 の一般の基礎環でのアフィン切断。
-/
def affineCoefficientBaseChangeSheafIso :
    letI : Algebra R (H ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
    (tensorCoefficientSheaf (H ⊗[A] R) (Scheme.ΓSpecIso R).inv.hom).ring ≅
      (tensorCoefficientSheaf H (affineBaseMap A R)).ring := by
  letI : Algebra R (H ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
  exact (presheafToSheaf (Opens.grothendieckTopology (Spec R)) RingCat).mapIso
    (affineCoefficientBaseChangeIso A R H)

/--
概要：底変換の層同型は前層から層化への比較射と可換。
方針：層化の単位の自然性を指定した前層同型へ適用する。
規約：抽象的な存在ではなく構成した同型の可換式。
使われ方：KST D4、Toën §3.2 の基本開での同型判定の移送。
-/
lemma affineCoefficientBaseChangeSheafIso_fac :
    letI : Algebra R (H ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
    (affineCoefficientBaseChangeIso A R H).hom ≫
        tensorCoefficientComparison H (affineBaseMap A R) =
      tensorCoefficientComparison (H ⊗[A] R) (Scheme.ΓSpecIso R).inv.hom ≫
        (affineCoefficientBaseChangeSheafIso A R H).hom.hom := by
  let : Algebra R (H ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
  exact toSheafify_naturality (Opens.grothendieckTopology (Spec R))
    (affineCoefficientBaseChangeIso A R H).hom

/--
概要：係数環層の底変換の同型は構造層からの射と可換。
方針：前層の単位との可換式と層化の単位の自然性を合成する。
規約：環層の同型を O 加群の同型へ移すための指定された可換式。
使われ方：KST D4、Toën §3.2 の正則加群の底変換。
-/
lemma affineCoefficientBaseChangeSheafIso_structureMap :
    letI : Algebra R (H ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
    (tensorCoefficientSheaf (H ⊗[A] R) (Scheme.ΓSpecIso R).inv.hom).structureMap ≫
      (affineCoefficientBaseChangeSheafIso A R H).hom =
    (tensorCoefficientSheaf H (affineBaseMap A R)).structureMap := by
  let : Algebra R (H ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
  apply Sheaf.hom_ext
  change coefficientTensorUnit (H ⊗[A] R) (Scheme.ΓSpecIso R).inv.hom ≫
      (toSheafify _ _ ≫ sheafifyMap _ (affineCoefficientBaseChangeIso A R H).hom) =
    coefficientTensorUnit H (affineBaseMap A R) ≫ toSheafify _ _
  rw [← toSheafify_naturality, ← Category.assoc, affineCoefficientBaseChangeIso_unit]

/--
概要：一般の A → R に対する係数環層の比較は基本開切断で環の同型。
方針：底変換の可換式で、R 係数の基本開比較の同型性を移送する。
規約：H は任意の結合 A 代数。
使われ方：KST D4、Toën §3.2 の一般のアフィン係数模型。
-/
instance affineBaseCoefficientComparison_basic_isIso (f : R) :
    IsIso ((tensorCoefficientComparison H (affineBaseMap A R)).app
      (.op (PrimeSpectrum.basicOpen f))) := by
  let : Algebra R (H ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
  let U := Opposite.op (PrimeSpectrum.basicOpen f)
  have h := congr_app (affineCoefficientBaseChangeSheafIso_fac A R H) U
  change (affineCoefficientBaseChangeIso A R H).hom.app U ≫
      (tensorCoefficientComparison H (affineBaseMap A R)).app U =
    (tensorCoefficientComparison (H ⊗[A] R) (Scheme.ΓSpecIso R).inv.hom).app U ≫
      (affineCoefficientBaseChangeSheafIso A R H).hom.hom.app U at h
  have : IsIso ((tensorCoefficientComparison (H ⊗[A] R)
      (Scheme.ΓSpecIso R).inv.hom).app U) :=
    affineCoefficientComparison_basic_isIso (H ⊗[A] R) f
  have : IsIso ((affineCoefficientBaseChangeSheafIso A R H).hom.hom.app U) :=
    inferInstanceAs (IsIso (((sheafToPresheaf (Opens.grothendieckTopology (Spec R))
      RingCat).mapIso (affineCoefficientBaseChangeSheafIso A R H)).hom.app U))
  have : IsIso ((affineCoefficientBaseChangeIso A R H).hom.app U ≫
      (tensorCoefficientComparison H (affineBaseMap A R)).app U) := by
    erw [h]
    infer_instance
  exact IsIso.of_isIso_comp_left ((affineCoefficientBaseChangeIso A R H).hom.app U) _

/--
概要：一般の A → R に対する係数環層の比較はアフィン全体の切断で環の同型。
方針：単位元による基本開が全体であることを使う。
規約：H の平坦性は要求しない。
使われ方：KST D4、Toën §3.2 の大域切断のアフィン計算。
-/
instance affineBaseCoefficientComparison_top_isIso :
    IsIso ((tensorCoefficientComparison H (affineBaseMap A R)).app (.op ⊤)) := by
  have h := affineBaseCoefficientComparison_basic_isIso A R H (1 : R)
  rw! [PrimeSpectrum.basicOpen_one] at h
  exact h

end SerrePositivity.KST.DerivedGeometry
