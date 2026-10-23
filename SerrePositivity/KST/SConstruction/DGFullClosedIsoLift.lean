module
public import SerrePositivity.KST.SConstruction.DGPerfectClosedIsoLift

/-! # 元の閉同型と全 Hom 前後合成を保つ充満部分圏への持ち上げ
概要：指定対象を含む充満 dg 部分圏へ、元の閉同型と全 Hom の前後合成を保持して戻す。
方針：元の Hom・単位・合成を継承する充満部分圏の構造を使う。
規約：同型の射を選び直さない。使われ方：同じ cone 点を含む小さい Perf 模型の比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] (P : D → Prop)
  (x y : DGFullSubcategory D P)
  (e : ForgetEnrichment.of (Complex R) x.val ≅ ForgetEnrichment.of (Complex R) y.val)

/-- 元の順逆の閉射を保つ、同じ充満 dg 部分圏への同型の持ち上げ。 -/
def dgFullClosedIsoLift : ForgetEnrichment.of (Complex R) x ≅
    ForgetEnrichment.of (Complex R) y where
  hom := e.hom
  inv := e.inv
  hom_inv_id := e.hom_inv_id
  inv_hom_id := e.inv_hom_id

/-- 持ち上げた順射による全 Hom 後合成は、元の後合成を回収する。 -/
lemma dgFullClosedIsoLift_whiskerLeft (z : DGFullSubcategory D P) :
    eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) z)
      (dgFullClosedIsoLift R D P x y e).hom =
    eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) z.val) e.hom := rfl

/-- 持ち上げた順射による全 Hom 前合成も、元の前合成を回収する。 -/
lemma dgFullClosedIsoLift_whiskerRight (z : DGFullSubcategory D P) :
    eHomWhiskerRight (Complex R) (dgFullClosedIsoLift R D P x y e).hom
      (ForgetEnrichment.of (Complex R) z) =
    eHomWhiskerRight (Complex R) e.hom (ForgetEnrichment.of (Complex R) z.val) := rfl

section Perfect
variable (E : Type v) [DGCategory R E] [Small.{u} E]
  (M N L : PerfectDGModule R E)
  (a : ForgetEnrichment.of (Complex R) M.val ≅ ForgetEnrichment.of (Complex R) N.val)

/-- 同じ Perf 持ち上げの全 Hom 後合成は、元の実加群の後合成。 -/
lemma dgPerfectClosedIsoLift_whiskerLeft :
    eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) L)
      (dgPerfectClosedIsoLift R E M N a).hom =
    eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) L.val) a.hom := rfl

/-- 同じ Perf 持ち上げの全 Hom 前合成も、元の実加群の前合成。 -/
lemma dgPerfectClosedIsoLift_whiskerRight :
    eHomWhiskerRight (Complex R) (dgPerfectClosedIsoLift R E M N a).hom
      (ForgetEnrichment.of (Complex R) L) =
    eHomWhiskerRight (Complex R) a.hom (ForgetEnrichment.of (Complex R) L.val) := rfl
end Perfect

end SerrePositivity.KST.SConstruction
