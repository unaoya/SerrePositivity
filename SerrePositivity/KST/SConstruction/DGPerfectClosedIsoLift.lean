module
public import SerrePositivity.DifferentialGraded.Perfect.Compact.Enhancement

/-! # 元の閉射を保持する実 perfect 加群同型の持ち上げ
概要：実加群の指定閉同型を、同じ成分のまま perfect 充満部分圏へ持ち上げる。
方針：同じ全 Hom・単位・合成を継承する充満 dg 部分圏の構造を使う。
規約：順逆の射を選び直さない。使われ方：評価済み cone の元の同型の実 Perf 比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]
  (M N : PerfectDGModule R E)
  (e : ForgetEnrichment.of (Complex R) M.val ≅ ForgetEnrichment.of (Complex R) N.val)

/-- 指定した実同型を、元の順逆の閉射のまま同じ実 Perf 内へ持ち上げる。 -/
def dgPerfectClosedIsoLift : ForgetEnrichment.of (Complex R) M ≅
    ForgetEnrichment.of (Complex R) N where
  hom := e.hom
  inv := e.inv
  hom_inv_id := e.hom_inv_id
  inv_hom_id := e.inv_hom_id

/-- 同じ持ち上げの順射を含めると、元の順射を回収する。 -/
lemma dgPerfectClosedIsoLift_hom :
    (perfectDGModuleInclusion R E Set.univ).onClosed.map
      (dgPerfectClosedIsoLift R E M N e).hom = e.hom := by
  change ForgetEnrichment.homOf (Complex R)
    (ForgetEnrichment.homTo (Complex R) e.hom ≫ 𝟙 _) = e.hom
  rw [Category.comp_id, ForgetEnrichment.homOf_homTo]

/-- 同じ持ち上げの逆射を含めると、元の逆射を回収する。 -/
lemma dgPerfectClosedIsoLift_inv :
    (perfectDGModuleInclusion R E Set.univ).onClosed.map
      (dgPerfectClosedIsoLift R E M N e).inv = e.inv := by
  change ForgetEnrichment.homOf (Complex R)
    (ForgetEnrichment.homTo (Complex R) e.inv ≫ 𝟙 _) = e.inv
  rw [Category.comp_id, ForgetEnrichment.homOf_homTo]

end SerrePositivity.KST.SConstruction
