module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.ProductChartCover
public import SerrePositivity.AlgebraicGeometry.AffineUniversal

/-!
概要：KST §5、Stacks 080Y の積中心によるアフィン blowup の共通細分。
方針：積生成元 ab のチャートから各因子の blowup への正則な持ち上げを貼り合わせる。
規約：実際の射を構成し、有限生成性も Noether 性も要求しない。
使われ方：有限個の admissible blowup の共通支配。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
variable {R : Type u} [CommRing R] (I J : Ideal R)

/--
概要：積中心の ab チャートから第一の中心の blowup への射。
方針：チャート上で I が正則な a により生成されることから普遍写像を作る。
規約：KST §5、Stacks 080Y、始域は実際の斉次局所化環の Spec。
使われ方：積中心の共通細分の局所成分。
-/
def productBlowupLeftChartMap (a : I) (b : J) :
    Spec (.of (BlowupChartRing (I * J) (mulCenterElement I J a b))) ⟶ affineBlowup I :=
  affineBlowupRegularLift I (chartBaseMap (I * J) (mulCenterElement I J a b)) a
    (productChart_left_regular I J a b) (productChart_left_image I J a b)

set_option backward.isDefEq.respectTransparency false in
/--
概要：積中心チャートの第一の比較射は基底上の射。
方針：正則な持ち上げの係数保存とチャート構造射を使う。
規約：KST §5、Stacks 080Y、基底は Spec R。
使われ方：局所比較射の重なり上の一致。
-/
@[reassoc] theorem productBlowupLeftChartMap_base (a : I) (b : J) :
    productBlowupLeftChartMap I J a b ≫ affineBlowupπ I =
      affineBlowupChartι (I * J) (mulCenterElement I J a b) ≫ affineBlowupπ (I * J) := by
  rw [productBlowupLeftChartMap, affineBlowupRegularLift_base]
  exact (affineBlowupChartIso_inv_ι_π (I * J) (mulCenterElement I J a b)).symm

set_option backward.isDefEq.respectTransparency false in
/--
概要：積中心の blowup から第一の中心の blowup への実際の比較射。
方針：積チャートの局所比較を分離性と中心外同型により貼り合わせる。
規約：KST §5、Stacks 080Y、任意の二つのイデアルを許す。
使われ方：admissible 中心の共通細分。
-/
def affineBlowupProductLeftMap : affineBlowup (I * J) ⟶ affineBlowup I :=
  (affineBlowupProductChartCover I J).openCover.glueMorphisms
    (fun p => productBlowupLeftChartMap I J p.1 p.2) (fun p q => by
      have hiso := affineBlowupπ_restrict_basicOpen_isIso I
        ⟨p.1.1 * p.2.1, I.mul_mem_right p.2.1 p.1.2⟩
      have : IsIso (affineBlowupπ I ∣_
          PrimeSpectrum.basicOpen (mulCenterElement I J p.1 p.2).1) := hiso
      exact chart_overlap_hom_ext (I * J) (affineBlowupπ I)
        (mulCenterElement I J p.1 p.2) (mulCenterElement I J q.1 q.2) _ _
        (productBlowupLeftChartMap_base I J p.1 p.2)
        (productBlowupLeftChartMap_base I J q.1 q.2))

set_option backward.isDefEq.respectTransparency false in
/--
概要：積中心から第一の中心への比較射は基底上で可換。
方針：積生成元のアフィン開被覆で局所交換式を使う。
規約：KST §5、Stacks 080Y、実際の構造射との等式。
使われ方：共通細分の可換三角形。
-/
@[reassoc] theorem affineBlowupProductLeftMap_base :
    affineBlowupProductLeftMap I J ≫ affineBlowupπ I = affineBlowupπ (I * J) := by
  apply (affineBlowupProductChartCover I J).openCover.hom_ext
  intro p
  simp only [affineBlowupProductLeftMap, Scheme.Cover.ι_glueMorphisms_assoc]
  exact productBlowupLeftChartMap_base I J p.1 p.2

/--
概要：積中心の blowup から第二の中心の blowup への実際の比較射。
方針：積の可換性で第一の比較射を移す。
規約：KST §5、Stacks 080Y、始域は Bl_{IJ}。
使われ方：二つの中心の共通細分の第二の射。
-/
def affineBlowupProductRightMap : affineBlowup (I * J) ⟶ affineBlowup J := by
  exact eqToHom (congrArg affineBlowup (mul_comm I J)) ≫ affineBlowupProductLeftMap J I

/--
概要：等しい中心の blowup の型変換は構造射と両立する。
方針：中心の等式による帰納法を使う。
規約：KST §5、これは二つの対象の定義的な置換だけを扱う。
使われ方：積の可換性による比較射の基底交換式。
-/
@[reassoc] theorem affineBlowup_eqToHom_base (K : Ideal R) (h : I = K) :
    eqToHom (congrArg affineBlowup h) ≫ affineBlowupπ K = affineBlowupπ I := by
  subst K
  simp

/--
概要：積中心から第二の中心への比較射は基底上で可換。
方針：積の可換性による第一の交換式の輸送を使う。
規約：KST §5、Stacks 080Y、Spec R への射の等式。
使われ方：共通細分の第二の可換三角形。
-/
@[reassoc] theorem affineBlowupProductRightMap_base :
    affineBlowupProductRightMap I J ≫ affineBlowupπ J = affineBlowupπ (I * J) := by
  unfold affineBlowupProductRightMap
  rw [Category.assoc, affineBlowupProductLeftMap_base,
    affineBlowup_eqToHom_base (I * J) (J * I) (mul_comm I J)]

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
