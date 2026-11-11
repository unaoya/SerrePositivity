module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FibrationInfinity
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeFunctorActionEvaluation

/-!
概要：元の cocartesian な底上の射に対応する豊穣 Hom を、全次数で評価する。
方針：core と相対条件の包含を通し、同じ元の射の curry に戻す。
規約：元の底上の射と全高次の相対 Hom を保持する。
使われ方：結合同型の共役と元の Segal 制限の比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 元の底上の射に対応する core の豊穣射は、包含後に同じ元の射の curry。 -/
lemma cocartesianNativeHomEquiv_ι {B : SSet.{u}}
    {p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory B} (f : p ⟶ q) :
    eHomEquiv SSet.{u} f ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.cocartesianRelativeFunctorSpace p.val.hom q.val.hom)).ι ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianRelativeFunctorInclusion p.val.hom q.val.hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom p.val.left).map q.val.hom) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p.val.hom) =
    curry' f.val.left := by
  apply (SSet.unitHomEquiv _).injective
  change (SSet.unitHomEquiv _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorHomEquiv p.val q.val f.val ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom p.val.left).map q.val.hom) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p.val.hom)) = _
  exact congrArg (SSet.unitHomEquiv _) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorHomEquiv_ι f.val)

/-- 同じ豊穣射は、任意の次数とパラメーター制限で元の全空間の射を評価する。 -/
lemma cocartesianNativeHomEquiv_apply {B : SSet.{u}}
    {p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory B} (f : p ⟶ q)
    {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m) (x : p.val.left.obj m) :
    (((eHomEquiv SSet.{u} f).app n PUnit.unit).val.val.val.app m α) x =
      f.val.left.app m x := by
  have h := congrArg (fun z ↦ ((z.app n PUnit.unit).app m α) x)
    (cocartesianNativeHomEquiv_ι f)
  exact h

/-- 元の core の豊穣前合成は、全ての局所 Hom に対する実際の前合成。 -/
lemma cocartesianNativeHomWhiskerRight_apply {B : SSet.{u}}
    {p p' q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory B} (f : p ⟶ p')
    {n m : SimplexCategoryᵒᵖ} (s : (SimplicialCategory.sHom p' q).obj n)
    (α : n ⟶ m) (x : p.val.left.obj m) :
    (((eHomWhiskerRight SSet.{u} f q).app n s).val.val.val.app m α) x =
      s.val.val.val.app m α (f.val.left.app m x) := by
  change (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition p.val p'.val q.val).app n
    (((eHomEquiv SSet.{u} f).app n PUnit.unit).val.val, s.val.val)).val.app m α) x = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorComposition_apply, cocartesianNativeHomEquiv_apply]

/-- 元の core の豊穣後合成は、全ての局所 Hom に対する実際の後合成。 -/
lemma cocartesianNativeHomWhiskerLeft_apply {B : SSet.{u}}
    {p q q' : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory B} (g : q ⟶ q')
    {n m : SimplexCategoryᵒᵖ} (s : (SimplicialCategory.sHom p q).obj n)
    (α : n ⟶ m) (x : p.val.left.obj m) :
    (((eHomWhiskerLeft SSet.{u} p g).app n s).val.val.val.app m α) x =
      g.val.left.app m (s.val.val.val.app m α x) := by
  change (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition p.val q.val q'.val).app n
    (s.val.val, ((eHomEquiv SSet.{u} g).app n PUnit.unit).val.val)).val.app m α) x = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorComposition_apply, cocartesianNativeHomEquiv_apply]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
