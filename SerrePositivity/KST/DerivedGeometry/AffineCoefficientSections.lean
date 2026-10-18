module

public import SerrePositivity.KST.DerivedGeometry.AffineCoefficientSheaf

/-!
# 係数環層のアフィン基本開切断

概要：Spec R 上の H ⊗_R O から係数環層への比較は基本開上で環の同型。
方針：tilde H との加法的比較の可換性から基礎写像の全単射性を得る。
規約：H の可換性・平坦性・有限性を要求しない。
使われ方：KST D4・T1′、Bondal–van den Bergh Thm 3.1.1、Toën §3.2。
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
概要：係数環前層からその層化への比較はアフィン基本開上で同型。
方針：指定された加法的比較の可換式と tilde の基本開切断の同型を使う。
規約：基礎環を R、スキームを Spec R とする標準構造射での主張。
使われ方：KST D4、Toën §3.2 の係数環層のアフィン模型。
-/
instance affineCoefficientComparison_basic_isIso (f : R) :
    IsIso ((tensorCoefficientComparison H (Scheme.ΓSpecIso R).inv.hom).app
      (.op (PrimeSpectrum.basicOpen f))) := by
  let U := Opposite.op (PrimeSpectrum.basicOpen f)
  let β := ((sheafToPresheaf (Opens.grothendieckTopology (Spec R))
    AddCommGrpCat).mapIso (affineCoefficientSheafAdditiveIso H)).hom.app U
  have : IsIso β := by dsimp [β]; infer_instance
  have h := congr_app (affineCoefficientSheafAdditiveIso_fac H) U
  change (forget₂ RingCat AddCommGrpCat).map
      ((tensorCoefficientComparison H (Scheme.ΓSpecIso R).inv.hom).app U) ≫ β =
    (affineCoefficientAdditiveIso H).hom.app U ≫
      (forget₂ (ModuleCat R) AddCommGrpCat).map
        ((affineTensorToTilde (ModuleCat.of R H)).app U) at h
  have : IsIso ((affineTensorToTilde (ModuleCat.of R H)).app U) :=
    affineTensorToTilde_basic_isIso _ f
  have : IsIso ((forget₂ RingCat AddCommGrpCat).map
      ((tensorCoefficientComparison H (Scheme.ΓSpecIso R).inv.hom).app U) ≫ β) := by
    rw [h]
    infer_instance
  have : IsIso ((forget₂ RingCat AddCommGrpCat).map
      ((tensorCoefficientComparison H (Scheme.ΓSpecIso R).inv.hom).app U)) :=
    (isIso_comp_right_iff _ β).mp inferInstance
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact ConcreteCategory.bijective_of_isIso
    ((forget₂ RingCat AddCommGrpCat).map
      ((tensorCoefficientComparison H (Scheme.ΓSpecIso R).inv.hom).app U))

/--
概要：アフィン全体の切断でも係数テンソルから層化への比較は同型。
方針：単位元による基本開が全体に等しいことを使う。
規約：任意の R 代数 H に対する環の同型判定。
使われ方：KST D4、Toën §3.2 のアフィン大域切断。
-/
instance affineCoefficientComparison_top_isIso :
    IsIso ((tensorCoefficientComparison H (Scheme.ΓSpecIso R).inv.hom).app
      (.op ⊤)) := by
  have h := affineCoefficientComparison_basic_isIso H (1 : R)
  rw! [PrimeSpectrum.basicOpen_one] at h
  exact h

end SerrePositivity.KST.DerivedGeometry
