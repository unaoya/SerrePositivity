module
public import SerrePositivity.KST.SConstruction.DGFullClosedIsoLift

/-!
概要：元の任意の閉零射を、同じ全 Hom を持つ充満 dg 部分圏へ持ち上げる。
方針：同じ射を使い、全 Hom の前後合成も厳密回収する。
規約：射の可逆性を要求しない。使われ方：実 cone 比較を共通小模型へ制限する。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] (P : D → Prop)
  (x y : DGFullSubcategory D P)
  (f : ForgetEnrichment.of (Complex R) x.val ⟶ ForgetEnrichment.of (Complex R) y.val)

/-- 概要：元の同じ閉射を充満 dg 部分圏の閉射へ持ち上げる。
方針：同じ全 Hom を使う。規約：元射を保持。
使われ方：元実射の所属圏を明示する。 -/
def dgFullClosedMapLift : ForgetEnrichment.of (Complex R) x ⟶
    ForgetEnrichment.of (Complex R) y := f

/-- 概要：同じ持ち上げによる全 Hom 後合成は元の後合成そのもの。
方針：継承した全 Hom を回収する。規約：元射を保持。
使われ方：閉射族の全次数自然性の制限。 -/
lemma dgFullClosedMapLift_whiskerLeft (z : DGFullSubcategory D P) :
    eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) z)
      (dgFullClosedMapLift R D P x y f) =
    eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) z.val) f := rfl

/-- 概要：同じ持ち上げによる全 Hom 前合成も元の前合成そのもの。
方針：継承した全 Hom を回収する。規約：元射を保持。
使われ方：閉射族の全次数自然性の制限。 -/
lemma dgFullClosedMapLift_whiskerRight (z : DGFullSubcategory D P) :
    eHomWhiskerRight (Complex R) (dgFullClosedMapLift R D P x y f)
      (ForgetEnrichment.of (Complex R) z) =
    eHomWhiskerRight (Complex R) f (ForgetEnrichment.of (Complex R) z.val) := rfl

section Perfect
variable (E : Type v) [DGCategory R E] [Small.{u} E]
  (M N L : PerfectDGModule R E)
  (a : ForgetEnrichment.of (Complex R) M.val ⟶ ForgetEnrichment.of (Complex R) N.val)

/-- 概要：元加群の閉射を同じ perfect 対象間の閉射に保持する。
方針：同じ全 Hom を継承する。規約：元射を保持。
使われ方：実逆回転の第一の閉射制限。 -/
def dgPerfectClosedMapLift : ForgetEnrichment.of (Complex R) M ⟶
    ForgetEnrichment.of (Complex R) N := a

/-- 概要：perfect 持ち上げの全 Hom 後合成は元の実加群の後合成。
方針：同じ全 Hom を回収する。規約：元射を保持。
使われ方：二段の小模型制限の全自然性。 -/
lemma dgPerfectClosedMapLift_whiskerLeft :
    eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) L)
      (dgPerfectClosedMapLift R E M N a) =
    eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) L.val) a := rfl

/-- 概要：perfect 持ち上げの全 Hom 前合成は元の実加群の前合成。
方針：同じ全 Hom を回収する。規約：元射を保持。
使われ方：二段の小模型制限の全自然性。 -/
lemma dgPerfectClosedMapLift_whiskerRight :
    eHomWhiskerRight (Complex R) (dgPerfectClosedMapLift R E M N a)
      (ForgetEnrichment.of (Complex R) L) =
    eHomWhiskerRight (Complex R) a (ForgetEnrichment.of (Complex R) L.val) := rfl
end Perfect
end SerrePositivity.KST.SConstruction
