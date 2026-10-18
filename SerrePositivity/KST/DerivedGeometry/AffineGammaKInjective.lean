module

public import SerrePositivity.KST.DerivedGeometry.AdjunctionKInjective
public import SerrePositivity.KST.DerivedGeometry.AffineTildeAdjunctionExact

/-!
概要：実際のアフィン係数大域切断は非有界 K-injective 複体を保つ。
方針：完全 tilde と大域切断の実際の随伴に一般の K-injective 移送を適用する。
規約：係数層圏の複体の有界性も H の平坦性も仮定しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の非有界導来比較の接続点。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry
namespace SerrePositivity.KST.DerivedGeometry
variable {R : CommRingCat.{u}} (H : Type u) [Ring H] [Algebra R H]

/--
概要：全係数層の K-injective 複体の項別大域切断は H 加群の K-injective 複体。
方針：完全左随伴の右随伴について証明した非有界の一般定理を使う。
規約：K-injective 分解の存在は別の構成で証明する。
使われ方：TT §3、Toën §3.2 の非有界右導来大域切断の計算。
-/
lemma affineCoefficientΓ_map_isKInjective
    (L : CochainComplex (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).Modules ℤ)
    [L.IsKInjective] :
    CochainComplex.IsKInjective
      (((affineCoefficientΓ (R := R) H).mapHomologicalComplex (.up ℤ)).obj L) :=
  rightAdjoint_map_isKInjective (affineCoefficientTildeAdjunction (R := R) H) L

end SerrePositivity.KST.DerivedGeometry
