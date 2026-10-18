module

public import SerrePositivity.KST.DerivedGeometry.AffineDerivedPlusUnit
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
概要：下に有界な加群導来圏から元の全係数層導来圏へのアフィン tilde は完全忠実。
方針：全対象の導来単位の同型性を随伴の完全忠実性判定へ適用する。
規約：非有界 tilde の完全忠実性とは区別する。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 のアフィン導来比較。
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
概要：bounded below アフィン導来随伴の単位は自然同型。
方針：全対象で既証の単位の同型性を束ねる。
規約：元の全係数層圏から右導来を作る。
使われ方：TT §3、Toën §3.2 の完全忠実性判定。
-/
instance affineDerivedPlus_unit_nat_isIso :
    IsIso (affineDerivedPlusAdjunction (R := R) H).unit := by
  have (K : DerivedCategory.Plus (ModuleCat.{u} H)) :
      IsIso ((affineDerivedPlusAdjunction (R := R) H).unit.app K) :=
    affineDerivedPlus_unit_isIso H K
  exact NatIso.isIso_of_isIso_app _

/--
概要：実際の bounded below アフィン tilde は完全忠実。
方針：実際の導来随伴の単位の同型性を適用する。
規約：標的は元の全係数層の bounded below 導来圏。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 のアフィン比較の完全忠実な方向。
-/
def affineDerivedTildePlusFullyFaithful : (affineDerivedTildePlus (R := R) H).FullyFaithful :=
  (affineDerivedPlusAdjunction (R := R) H).fullyFaithfulLOfIsIsoUnit

/-- 概要：bounded below tilde は充満。方針：証明済みの完全忠実性を取り出す。
規約：元の全層導来圏が標的。使われ方：TT §3、Toën §3.2 のアフィンの射の比較。 -/
instance affineDerivedTildePlus_full : (affineDerivedTildePlus (R := R) H).Full :=
  (affineDerivedTildePlusFullyFaithful (R := R) H).full

/-- 概要：bounded below tilde は忠実。方針：証明済みの完全忠実性を取り出す。
規約：元の全層導来圏が標的。使われ方：TT §3、Toën §3.2 のアフィンの射の比較。 -/
instance affineDerivedTildePlus_faithful : (affineDerivedTildePlus (R := R) H).Faithful :=
  (affineDerivedTildePlusFullyFaithful (R := R) H).faithful

end SerrePositivity.KST.DerivedGeometry
