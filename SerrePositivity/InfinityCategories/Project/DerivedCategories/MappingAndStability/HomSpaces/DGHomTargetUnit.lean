module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.DGModuleUnitPinchedModel
public import SerrePositivity.DifferentialGraded.Module.Left.CategoryComparison
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] (x : C)
/-- 一般 dg 対象 x からの全 Hom を R 加群に送る同じ dg 関手。 -/
def dgHomTargetModuleDG : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R PUnit.{1}) :=
  (_root_.SerrePositivity.DifferentialGraded.leftRepresentable R x).comp (_root_.SerrePositivity.DifferentialGraded.ringConstantDG R)
/-- Hom(x,x) の単位を Yoneda 拡張した、同じ R 代表加群からの閉射。 -/
def dgHomTargetUnit :
    ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (_root_.SerrePositivity.DifferentialGraded.representable R PUnit.unit) ⟶
      ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) ((dgHomTargetModuleDG R C x).obj x) :=
  ForgetEnrichment.homOf (_root_.SerrePositivity.DifferentialGraded.Complex R)
    (eId (_root_.SerrePositivity.DifferentialGraded.Complex R) x ≫ (_root_.SerrePositivity.DifferentialGraded.dgYonedaIso R PUnit.unit ((dgHomTargetModuleDG R C x).obj x)).inv)
/-- 同じ閉射を全 Hom の Yoneda 評価へ戻すと、元の dg 単位そのもの。 -/
lemma dgHomTargetUnit_evaluation :
    ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex R) (dgHomTargetUnit R C x) ≫
      (_root_.SerrePositivity.DifferentialGraded.dgYonedaIso R PUnit.unit ((dgHomTargetModuleDG R C x).obj x)).hom =
    eId (_root_.SerrePositivity.DifferentialGraded.Complex R) x := by
  dsimp only [dgHomTargetUnit, ForgetEnrichment.homTo_homOf]
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
