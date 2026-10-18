module

public import SerrePositivity.KST.DerivedGeometry.AffineCoefficientSections
public import SerrePositivity.KST.DerivedGeometry.TensorCoefficientAction

/-!
# アフィン係数環層の構造層加群

概要：係数環層の正則加群を構造層上へ忘れ、tilde からの標準射を構成する。
方針：H の定数切断の R 線形性と tilde の随伴を使う。
規約：準連接性とコンパクト生成はそれぞれ別の証明として扱う。
使われ方：KST D4・T1、Bondal–van den Bergh Thm 3.1.1、Toën §3.2。
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
概要：係数環層の正則左加群を構造層上の加群層とする。
方針：係数環層自身の単位加群へスカラー制限を適用する。
規約：係数環の可換性を要求しない。
使われ方：KST D4、Toën §3.2 の係数環層の準連接性。
-/
def CoefficientSheaf.regular {X : Scheme.{u}} (B : CoefficientSheaf X) : X.Modules :=
  B.forget.obj (SheafOfModules.unit B.ring)

variable {R : CommRingCat.{u}} (H : Type u) [Ring H] [Algebra R H]

/--
概要：定数切断による H から係数環層の正則加群の大域切断への R 線形写像。
方針：H と構造層からの基礎環の作用の一致を使う。
規約：標準構造射 Spec R 上で構成する。
使われ方：KST D4、Toën §3.2 の tilde からの比較射。
-/
def affineCoefficientConstantLinear :
    ModuleCat.of R H ⟶ moduleSpecΓFunctor.obj
      (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).regular := by
  change ModuleCat.of R H ⟶ ModuleCat.of R
    Γ((tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).regular, ⊤)
  exact ModuleCat.ofHom (show H →ₗ[R]
    Γ((tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).regular, ⊤) from {
    toFun := (tensorCoefficientConstant H (Scheme.ΓSpecIso R).inv.hom).app (.op ⊤)
    map_add' := map_add _
    map_smul' r h := by
      change ((tensorCoefficientConstant H (Scheme.ΓSpecIso R).inv.hom).app (.op ⊤))
          (r • h) =
        (((tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).structureMap.hom).app
          (.op ⊤)) (sectionBaseMap (Scheme.ΓSpecIso R).inv.hom ⊤ r) *
            ((tensorCoefficientConstant H (Scheme.ΓSpecIso R).inv.hom).app (.op ⊤)) h
      rw [Algebra.smul_def, map_mul]
      congr 1
      exact congrArg (fun g : R →+* _ => g r)
        (tensorCoefficientConstant_comp_algebraMap H (Scheme.ΓSpecIso R).inv.hom ⊤) })

/--
概要：tilde H から係数環層の正則 O 加群への標準射。
方針：定数切断を tilde 関手で送り、大域切断随伴の余単位と合成する。
規約：環層としての比較ではなく構造層加群の射を構成する。
使われ方：KST D4、Toën §3.2 のアフィン準連接性の比較。
-/
def affineCoefficientModuleMap :
    tilde (ModuleCat.of R H) ⟶
      (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).regular :=
  tilde.map (affineCoefficientConstantLinear H) ≫
    (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).regular.fromTildeΓ

/--
概要：標準射は H の標準切断を、定数切断の制限へ送る。
方針：tilde の自然性と随伴の余単位の切断上の式を合成する。
規約：任意の開での R 加群射の等式として述べる。
使われ方：KST D4、Toën §3.2 の基本開上の比較。
-/
lemma toOpen_affineCoefficientModuleMap (U : (Spec R).Opens) :
    tilde.toOpen (ModuleCat.of R H) U ≫
      (modulesSpecToSheaf.map (affineCoefficientModuleMap H)).hom.app (.op U) =
    affineCoefficientConstantLinear H ≫
      (modulesSpecToSheaf.obj
        (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).regular).obj.map
          (homOfLE le_top).op := by
  change tilde.toOpen (ModuleCat.of R H) U ≫
    ((modulesSpecToSheaf.map (tilde.map (affineCoefficientConstantLinear H))).hom.app
        (.op U) ≫
      (modulesSpecToSheaf.map
        (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).regular.fromTildeΓ).hom.app
          (.op U)) = _
  erw [tilde.toOpen_map_app_assoc, Scheme.Modules.toOpen_fromTildeΓ_app]

/--
概要：H の元の標準切断は同じ元の係数環層の定数切断に送られる。
方針：標準切断に関する射の等式を評価し、定数切断の自然性を使う。
規約：任意の開での切断上の等式。
使われ方：KST D4、Toën §3.2 の純テンソル上の比較計算。
-/
lemma affineCoefficientModuleMap_standard (U : (Spec R).Opens) (h : H) :
    ((affineCoefficientModuleMap H).val.app (.op U)).hom
        (show Γ(tilde (ModuleCat.of R H), U) from
          (tilde.toOpen (ModuleCat.of R H) U).hom h) =
      ((tensorCoefficientConstant H (Scheme.ΓSpecIso R).inv.hom).app (.op U)) h := by
  have hc := congrArg (fun g : ModuleCat.of R H ⟶ ModuleCat.of R
      Γ((tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).regular, U) => g h)
    (toOpen_affineCoefficientModuleMap H U)
  exact hc.trans (NatTrans.naturality_apply
    (tensorCoefficientConstant H (Scheme.ΓSpecIso R).inv.hom)
    (homOfLE (show U ≤ ⊤ from le_top)).op h).symm

/--
概要：正則加群の比較は純テンソルの層化の像と一致する。
方針：O 線形性、標準切断の計算、テンソル因子の積の式を使う。
規約：右辺は係数環前層のスカラー構造を明示した純テンソル。
使われ方：KST D4、Toën §3.2 の基本開での同型判定。
-/
lemma affineCoefficientModuleMap_tmul (U : (Spec R).Opens)
    (h : H) (s : Γ(Spec R, U)) :
    ((affineCoefficientModuleMap H).val.app (.op U)).hom
      (affineTensorSectionMap (ModuleCat.of R H) U (h ⊗ₜ[R] s)) =
    ((tensorCoefficientComparison H (Scheme.ΓSpecIso R).inv.hom).app (.op U))
      (affineTensorAdditivePure H U
        (sectionAlgebra (Scheme.ΓSpecIso R).inv.hom U) h s) := by
  rw [affineTensorSectionMap_tmul, map_smul, affineCoefficientModuleMap_standard]
  let (V : (Spec R).Opens) : Algebra R Γ(Spec R, V) :=
    sectionAlgebra (Scheme.ΓSpecIso R).inv.hom V
  change ((tensorCoefficientComparison H (Scheme.ΓSpecIso R).inv.hom).app (.op U))
      (1 ⊗ₜ[R] s) *
    ((tensorCoefficientComparison H (Scheme.ΓSpecIso R).inv.hom).app (.op U))
      (h ⊗ₜ[R] 1) = _
  rw [← map_mul]
  congr 1
  change (1 ⊗ₜ[R] s : H ⊗[R] Γ(Spec R, U)) * (h ⊗ₜ[R] 1) = h ⊗ₜ[R] s
  simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

end SerrePositivity.KST.DerivedGeometry
