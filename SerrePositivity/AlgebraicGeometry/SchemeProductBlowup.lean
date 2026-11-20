module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.SchemeBlowup
public import SerrePositivity.AlgebraicGeometry.ProductNaturality

/-!
概要：KST §5、Stacks 080Y の一般スキーム上の積中心による共通細分。
方針：アフィン積中心の比較射を自然変換とし、スキームの余極限へ移す。
規約：同じ基礎スキーム上の二中心を扱い、blowup の合成とは区別する。
使われ方：admissible 中心の有限個の共通支配。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
variable {X : Scheme.{u}} (I J : X.IdealSheafData)

set_option backward.isDefEq.respectTransparency false in
/--
概要：積中心のアフィン blowup 図式から第一の中心の図式への自然変換。
方針：積中心の比較射の係数環写像に対する自然性を使う。
規約：KST §5、Stacks 080Y、アフィン開集合全体の順序圏を添字とする。
使われ方：一般スキーム上の共通細分の射の構成。
-/
def affineBlowupProductLeftNatTrans : affineBlowupDiagram (I * J) ⟶ affineBlowupDiagram I where
  app U := affineBlowupProductLeftMap (I.ideal U) (J.ideal U)
  naturality U V h := by
    have hI : (I.ideal V).map (affineModelRestriction (leOfHom h)) = I.ideal U :=
      I.map_ideal (leOfHom h)
    have hJ : (J.ideal V).map (affineModelRestriction (leOfHom h)) = J.ideal U :=
      J.map_ideal (leOfHom h)
    change affineBlowupCenterMap (I.ideal V * J.ideal V) (I.ideal U * J.ideal U)
        (affineModelRestriction (leOfHom h))
        (by rw [Ideal.map_mul, hI, hJ]) ≫
        affineBlowupProductLeftMap (I.ideal V) (J.ideal V) =
      affineBlowupProductLeftMap (I.ideal U) (J.ideal U) ≫
        affineBlowupCenterMap (I.ideal V) (I.ideal U)
          (affineModelRestriction (leOfHom h)) (I.map_ideal (leOfHom h))
    exact affineBlowupProductLeftMap_naturality (I.ideal V) (J.ideal V)
      (I.ideal U) (J.ideal U) (affineModelRestriction (leOfHom h))
      (I.map_ideal (leOfHom h)) (J.map_ideal (leOfHom h))

/--
概要：一般スキームの積中心の blowup から第一の中心の blowup への実際の射。
方針：アフィン局所図式の自然変換に余極限の関手を適用する。
規約：KST §5、Stacks 080Y、有限生成性や Noether 性は不要。
使われ方：同じ基底上の二つの blowup の共通細分。
-/
def blowupProductLeftMap : blowup (I * J) ⟶ blowup I :=
  colimMap (affineBlowupProductLeftNatTrans I J)

set_option backward.isDefEq.respectTransparency false in
/--
概要：一般の積中心の比較射はアフィン局所モデルの比較射に制限される。
方針：余極限の自然変換の標準射との交換式を使う。
規約：KST §5、Stacks 080Y、第一の中心への射。
使われ方：大域比較射の構造射との両立性。
-/
@[reassoc] theorem blowupAffineι_blowupProductLeftMap (U : X.affineOpens) :
    blowupAffineι (I * J) U ≫ blowupProductLeftMap I J =
      affineBlowupProductLeftMap (I.ideal U) (J.ideal U) ≫ blowupAffineι I U := by
  exact ι_colimMap (affineBlowupProductLeftNatTrans I J) U

set_option backward.isDefEq.respectTransparency false in
/--
概要：一般の積中心から第一の中心への比較射は基底上で可換。
方針：各アフィン局所モデルの比較射の構造射との両立性を使う。
規約：KST §5、Stacks 080Y、元の基礎スキーム X への射。
使われ方：admissible な共通細分の可換三角形。
-/
@[reassoc] theorem blowupProductLeftMap_base :
    blowupProductLeftMap I J ≫ blowupπ I = blowupπ (I * J) := by
  apply colimit.hom_ext
  intro U
  change blowupAffineι (I * J) U ≫ blowupProductLeftMap I J ≫ blowupπ I =
    blowupAffineι (I * J) U ≫ blowupπ (I * J)
  rw [blowupAffineι_blowupProductLeftMap_assoc, blowupAffineι_π, blowupAffineι_π]
  unfold affineBlowupModelToBase affineBlowupModelπ
  rw [← Category.assoc, ← Category.assoc, affineBlowupProductLeftMap_base]
  rfl

/--
概要：等しい中心の一般 blowup の型変換は構造射と両立する。
方針：中心の等式による帰納法を使う。
規約：KST §5、同じ基底上のイデアル層の等式を扱う。
使われ方：積の可換性による共通細分の第二の射。
-/
@[reassoc] theorem blowup_eqToHom_base (K : X.IdealSheafData) (h : I = K) :
    eqToHom (congrArg blowup h) ≫ blowupπ K = blowupπ I := by
  subst K
  simp

/--
概要：一般スキームの積中心の blowup から第二の中心の blowup への実際の射。
方針：積の可換性で第一の比較射を移す。
規約：KST §5、Stacks 080Y、始域は Bl_{IJ}。
使われ方：共通細分の第二の可換三角形。
-/
def blowupProductRightMap : blowup (I * J) ⟶ blowup J :=
  eqToHom (congrArg blowup (mul_comm I J)) ≫ blowupProductLeftMap J I

/--
概要：一般の積中心から第二の中心への比較射は基底上で可換。
方針：第一の交換式と等しい中心の構造射の輸送を使う。
規約：KST §5、Stacks 080Y、元の基礎スキーム X への等式。
使われ方：二中心の共通支配。
-/
@[reassoc] theorem blowupProductRightMap_base :
    blowupProductRightMap I J ≫ blowupπ J = blowupπ (I * J) := by
  unfold blowupProductRightMap
  rw [Category.assoc, blowupProductLeftMap_base,
    blowup_eqToHom_base (I * J) (J * I) (mul_comm I J)]

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
