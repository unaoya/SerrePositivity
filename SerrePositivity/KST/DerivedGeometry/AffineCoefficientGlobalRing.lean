module

public import SerrePositivity.KST.DerivedGeometry.AffineCoefficientQuasicoherent

/-!
# アフィン係数環層の大域切断環

概要：Spec R 上の係数環層の大域切断環を指定された定数切断 H と同定する。
方針：正則 O 加群の tilde との同型と tilde の大域切断を使う。
規約：単なる環同型の存在でなく h を定数切断へ送る写像を使う。
使われ方：KST D4・T1′、Toën Derived Azumaya §3.2 の大域切断関手。
-/

@[expose] public section

noncomputable section

set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

namespace SerrePositivity.KST.DerivedGeometry

variable {R : CommRingCat.{u}} (H : Type u) [Ring H] [Algebra R H]

/--
概要：H から正則 O 加群の大域切断への指定された線形写像は同型。
方針：tilde の標準切断と正則加群の比較射の大域切断の合成に同定する。
規約：H の有限性・平坦性は不要。
使われ方：KST D4、Toën §3.2 の大域切断環の全単射性。
-/
instance affineCoefficientConstantLinear_isIso :
    IsIso (affineCoefficientConstantLinear (R := R) H) := by
  have h := toOpen_affineCoefficientModuleMap (R := R) H ⊤
  change tilde.toOpen (ModuleCat.of R H) ⊤ ≫
      (modulesSpecToSheaf.map (affineCoefficientModuleMap H)).hom.app (.op ⊤) =
    affineCoefficientConstantLinear H ≫
      (modulesSpecToSheaf.obj
        (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).regular).obj.map (𝟙 _) at h
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at h
  erw [← h]
  infer_instance

/--
概要：H の定数切断はアフィン係数環層の大域切断環と環同型を与える。
方針：同じ写像の R 線形な同型性から基礎写像の全単射性を得る。
規約：環層の大域切断の比較であり、H の可換性は不要。
使われ方：KST D4・T1′、Toën §3.2 の係数加群の大域切断。
-/
instance affineCoefficientConstant_top_isIso :
    IsIso ((tensorCoefficientConstant H (Scheme.ΓSpecIso R).inv.hom).app (.op ⊤)) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact ConcreteCategory.bijective_of_isIso (affineCoefficientConstantLinear (R := R) H)

/--
概要：アフィン係数環層の大域切断環と H の標準同型。
方針：指定された定数切断の環射を同型として束ねる。
規約：同型の向きは H から大域切断へ。
使われ方：KST D4、Toën §3.2 のアフィン係数加群の関手。
-/
def affineCoefficientGlobalIso : RingCat.of H ≅
    (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).ring.obj.obj (.op ⊤) :=
  asIso ((tensorCoefficientConstant H (Scheme.ΓSpecIso R).inv.hom).app (.op ⊤))

end SerrePositivity.KST.DerivedGeometry
