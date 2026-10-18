module

public import SerrePositivity.KST.DerivedGeometry.AffineDerivedPlus
public import SerrePositivity.KST.DerivedGeometry.RightDerivedPlusSingleBounds

/-!
概要：アフィン上の準連接係数層の右導来大域切断は次数零に集中する。
方針：実際の係数層の injective 分解と既証の正次数切断消滅を適用する。
規約：H は非可換でもよく、平坦性を要求しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の単一層でのアフィン比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry
namespace SerrePositivity.KST.DerivedGeometry
variable {R : CommRingCat.{u}} (H : Type u) [Ring H] [Algebra R H]
  [HasDerivedCategory (ModuleCat.{u} H)]
  [HasDerivedCategory (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).Modules]

/--
概要：準連接係数層の単一複体の右導来大域切断は次数零以上。
方針：一般の右導来関手の下限保存を適用する。
規約：元の全係数層の導来圏で計算する。
使われ方：TT §3、Toën §3.2 のアフィン比較の下限。
-/
instance affineDerivedΓPlus_single_isGE
    (F : (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).QCoh) :
    ((affineDerivedΓPlus (R := R) H).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F.obj)).IsGE 0 :=
  rightDerivedPlus_single_isGE (affineCoefficientΓ (R := R) H) F.obj

/--
概要：準連接係数層の単一複体の右導来大域切断は次数零以下。
方針：元の係数層圏における高次大域切断の消滅を単一対象の比較へ代入する。
規約：準連接層の圏で分解することへ置換しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 のアフィン導来比較。
-/
lemma affineDerivedΓPlus_single_isLE
    (F : (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).QCoh) :
    ((affineDerivedΓPlus (R := R) H).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F.obj)).IsLE 0 :=
  rightDerivedPlus_single_isLE (affineCoefficientΓ (R := R) H) F.obj
    (affineCoefficientΓ_rightDerived_isZero H F)

end SerrePositivity.KST.DerivedGeometry
