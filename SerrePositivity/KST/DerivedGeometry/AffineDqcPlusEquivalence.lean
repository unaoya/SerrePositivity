module

public import SerrePositivity.KST.DerivedGeometry.AffineDerivedPlusCounit

/-!
概要：アフィン上の下に有界な加群導来圏と実際の準連接コホモロジー対象の同値。
方針：完全忠実な tilde を値域へ持ち上げ、実際の導来余単位で全対象の像を構成する。
規約：非有界アフィン同値とは別。D(QCoh) への置換や冪等完備化は行わない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 のアフィン比較の bounded below 段階。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry
namespace SerrePositivity.KST.DerivedGeometry
namespace CoefficientSheaf
variable {X : Scheme.{u}} (B : CoefficientSheaf X) [HasDerivedCategory B.Modules]

/--
概要：元の全係数層の下に有界な導来圏における準連接コホモロジー条件。
方針：元の非有界 Dqc の条件を包含で引き戻す。
規約：新しい複体模型へ置換しない。
使われ方：TT §3、Toën §3.2 の bounded below の比較先。
-/
def hasQuasicoherentCohomologyPlus : ObjectProperty (DerivedCategory.Plus B.Modules) :=
  fun K => B.hasQuasicoherentCohomology K.obj

/--
概要：実際の Dqc の下に有界な対象の充満部分圏。
方針：全層の下に有界な導来対象へ同じ準連接コホモロジー条件を添える。
規約：層の複体の導来圏が母圏。
使われ方：TT §3・§8、Toën §3.2 のアフィン導来比較。
-/
abbrev DqcPlus := B.hasQuasicoherentCohomologyPlus.FullSubcategory
end CoefficientSheaf

variable {R : CommRingCat.{u}} (H : Type u) [Ring H] [Algebra R H]
  [HasDerivedCategory (ModuleCat.{u} H)]
  [HasDerivedCategory (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).Modules]

/--
概要：下に有界な tilde を実際の Dqc の下に有界な対象へ制限する。
方針：非有界 tilde の既証の準連接コホモロジー判定を同じ対象に用いる。
規約：元の層導来対象と射を保持する。
使われ方：TT §3、Toën §3.2 のアフィン同値の順方向。
-/
def affineDerivedTildePlusToDqc : DerivedCategory.Plus (ModuleCat.{u} H) ⥤
    (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).DqcPlus :=
  ObjectProperty.lift _ (affineDerivedTildePlus (R := R) H)
    (fun K => affineDerivedTilde_hasQuasicoherentCohomology H K.obj)

/--
概要：Dqc へ制限した bounded below tilde は完全忠実。
方針：元の全層導来圏への包含との合成の完全忠実性を用いる。
規約：充満部分圏の包含は忠実。
使われ方：TT §3、Toën §3.2 のアフィンの射の比較。
-/
def affineDerivedTildePlusToDqcFullyFaithful :
    (affineDerivedTildePlusToDqc (R := R) H).FullyFaithful :=
  Functor.FullyFaithful.ofCompFaithful
    (F := affineDerivedTildePlusToDqc (R := R) H)
    (G := (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).hasQuasicoherentCohomologyPlus.ι)
    (affineDerivedTildePlusFullyFaithful (R := R) H)

/-- 概要：比較関手は充満。方針：完全忠実性の証明を取り出す。
規約：実際の DqcPlus。使われ方：TT §3、Toën §3.2 のアフィン同値。 -/
instance affineDerivedTildePlusToDqc_full : (affineDerivedTildePlusToDqc (R := R) H).Full :=
  (affineDerivedTildePlusToDqcFullyFaithful (R := R) H).full

/-- 概要：比較関手は忠実。方針：完全忠実性の証明を取り出す。
規約：実際の DqcPlus。使われ方：TT §3、Toën §3.2 のアフィン同値。 -/
instance affineDerivedTildePlusToDqc_faithful : (affineDerivedTildePlusToDqc (R := R) H).Faithful :=
  (affineDerivedTildePlusToDqcFullyFaithful (R := R) H).faithful

/--
概要：比較関手は冪等完備化を取らず本質的全射。
方針：各対象を右導来大域切断の tilde と実際の余単位で同型にする。
規約：像の存在は証明済みの余単位の同型性から構成する。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の bounded below アフィン同値。
-/
instance affineDerivedTildePlusToDqc_essSurj : (affineDerivedTildePlusToDqc (R := R) H).EssSurj where
  mem_essImage K := by
    have : IsIso ((affineDerivedPlusAdjunction (R := R) H).counit.app K.obj) :=
      affineDerivedPlus_counit_isIso H K.obj K.property
    exact ⟨(affineDerivedΓPlus (R := R) H).obj K.obj,
      ⟨ObjectProperty.isoMk _ (asIso ((affineDerivedPlusAdjunction (R := R) H).counit.app K.obj))⟩⟩

/-- 概要：実際の bounded below アフィン比較は同値関手。
方針：完全忠実性と構成済みの本質的全射性を束ねる。
規約：非有界比較と区別。使われ方：TT §3、Toën §3.2 のアフィン同値。 -/
instance affineDerivedTildePlusToDqc_isEquivalence :
    (affineDerivedTildePlusToDqc (R := R) H).IsEquivalence where

/--
概要：下に有界な H 加群の導来圏は実際のアフィン DqcPlus と同値。
方針：同じ tilde 比較の完全忠実性と実際の余単位による全射性から同値を構成する。
規約：H の可換性・平坦性や冪等完備化は不要。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の非有界比較へ向けた検証済み段階。
-/
def affineDqcPlusEquivalence : DerivedCategory.Plus (ModuleCat.{u} H) ≌
    (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).DqcPlus :=
  (affineDerivedTildePlusToDqc (R := R) H).asEquivalence

end SerrePositivity.KST.DerivedGeometry
