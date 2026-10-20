module
public import SerrePositivity.InfinityCategories.Derived.DGModuleUnitPinchedModel
public import SerrePositivity.DifferentialGraded.Module.RingDGComparison
/-!
概要：Hom(x,x) の同じ dg 単位から、R の代表加群を始域とする実閉射を作る。
方針：全 Hom の dg Yoneda 同型の逆で拡張し、同じ単位を回収する厳密等式を示す。
規約：H⁰ の類の選択を使わない。使われ方：実 Hom の全関手族の coslice 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] (x : C)
/-- 一般 dg 対象 x からの全 Hom を R 加群に送る同じ dg 関手。 -/
def dgHomTargetModuleDG : DGFunctor R C (RightModule R PUnit.{1}) :=
  (leftRepresentable R x).comp (ringConstantDG R)
/-- Hom(x,x) の単位を Yoneda 拡張した、同じ R 代表加群からの閉射。 -/
def dgHomTargetUnit :
    ForgetEnrichment.of (Complex R) (representable R PUnit.unit) ⟶
      ForgetEnrichment.of (Complex R) ((dgHomTargetModuleDG R C x).obj x) :=
  ForgetEnrichment.homOf (Complex R)
    (eId (Complex R) x ≫ (dgYonedaIso R PUnit.unit ((dgHomTargetModuleDG R C x).obj x)).inv)
/-- 同じ閉射を全 Hom の Yoneda 評価へ戻すと、元の dg 単位そのもの。 -/
lemma dgHomTargetUnit_evaluation :
    ForgetEnrichment.homTo (Complex R) (dgHomTargetUnit R C x) ≫
      (dgYonedaIso R PUnit.unit ((dgHomTargetModuleDG R C x).obj x)).hom =
    eId (Complex R) x := by
  dsimp only [dgHomTargetUnit, ForgetEnrichment.homTo_homOf]
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
end SerrePositivity.InfinityCategories
