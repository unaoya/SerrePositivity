module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.CompatibleChartIdeals
public import SerrePositivity.AlgebraicGeometry.SpecIdeal
public import SerrePositivity.AlgebraicGeometry.SchemeBlowupProper

/-!
概要：KST §5、Stacks 080Y の blowup 上の実際のイデアル層からの整合チャートイデアル。
方針：各チャートへの逆像を元の環のイデアルに移し、ファイバー積の交換式で整合性を示す。
規約：任意の整合族を仮定する代わりに、与えられた IdealSheafData から構成する。
使われ方：blowup 上の中心の基底への降下と合成の共通支配。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
variable {R : Type u} [CommRing R] (I : Ideal R)

/--
概要：blowup 上のイデアル層を標準チャート環のイデアルへ制限する。
方針：チャートへの逆像イデアル層に Spec のイデアル順序同型を適用する。
規約：KST §5、Stacks 080Y、元のイデアル層を保持する。
使われ方：実際の中心の降下に使うチャートイデアル族。
-/
def blowupChartIdeal (K : (affineBlowup I).IdealSheafData) (a : I) :
    Ideal (BlowupChartRing I a) :=
  specIdealEquiv (.of (BlowupChartRing I a)) (K.comap (affineBlowupChartι I a))

set_option backward.isDefEq.respectTransparency false in
/--
概要：重なりから二つの標準チャートを通る blowup への射は一致する。
方針：重なりのファイバー積同型の両射公式とファイバー積の可換性を使う。
規約：KST §5、Stacks 080Y、実際の環制限写像の Spec。
使われ方：イデアル層の逆像の重なり上の一致。
-/
theorem chartOverlap_to_blowup (a b : I) :
    Spec.map (CommRingCat.ofHom (chartOverlapFromLeft I a b)) ≫ affineBlowupChartι I a =
      Spec.map (CommRingCat.ofHom (chartOverlapFromRight I a b)) ≫ affineBlowupChartι I b := by
  rw [← affineBlowupChartOverlapIso_inv_fst_assoc,
    ← affineBlowupChartOverlapIso_inv_snd_assoc, pullback.condition]

set_option backward.isDefEq.respectTransparency false in
/--
概要：実際の blowup 上のイデアル層から得たチャートイデアル族は重なりで整合する。
方針：Spec の逆像公式を使い、両側を重なりへの同じ幾何学的逆像に同定する。
規約：KST §5、Stacks 080Y、有限生成性を要求しない。
使われ方：中心の降下における比の冪による所属の移送。
-/
theorem blowupChartIdeals_compatible (K : (affineBlowup I).IdealSheafData) :
    ChartIdealsCompatible I (blowupChartIdeal I K) := by
  intro a b
  unfold blowupChartIdeal
  have hL := specIdealEquiv_comap (CommRingCat.ofHom (chartOverlapFromLeft I a b))
    (K.comap (affineBlowupChartι I a))
  have hR := specIdealEquiv_comap (CommRingCat.ofHom (chartOverlapFromRight I a b))
    (K.comap (affineBlowupChartι I b))
  simp only [CommRingCat.hom_ofHom] at hL hR
  rw [← hL, ← hR,
    ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
    chartOverlap_to_blowup]

set_option backward.isDefEq.respectTransparency false in
/--
概要：Noether 環の blowup の標準チャート環も Noether。
方針：有限生成中心の blowup の有限型性を使い、開チャートへ局所 Noether 性を移す。
規約：KST §5、Stacks 080Y、中心の有限生成性は Noether 性から得る。
使われ方：各チャートの中心イデアルに有限分母消去を適用する。
-/
instance blowupChartRing_isNoetherianRing [IsNoetherianRing R] (a : I) :
    IsNoetherianRing (BlowupChartRing I a) := by
  have := affineBlowupπ_isProper I (Ideal.fg_of_isNoetherianRing I)
  have := LocallyOfFiniteType.isLocallyNoetherian (affineBlowupπ I)
  have := isLocallyNoetherian_of_isOpenImmersion (affineBlowupChartι I a)
  exact (isLocallyNoetherian_Spec (R := .of (BlowupChartRing I a))).mp inferInstance

/--
概要：Noether 環上の blowup の任意の中心は各標準チャートで有限生成。
方針：チャート環の Noether 性を使う。
規約：KST §5、Stacks 080Y、与えられたイデアル層の追加仮定は不要。
使われ方：実際の中心へ一チャート上のイデアル降下を適用する。
-/
theorem blowupChartIdeal_fg [IsNoetherianRing R]
    (K : (affineBlowup I).IdealSheafData) (a : I) : (blowupChartIdeal I K a).FG :=
  Ideal.fg_of_isNoetherianRing _

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
