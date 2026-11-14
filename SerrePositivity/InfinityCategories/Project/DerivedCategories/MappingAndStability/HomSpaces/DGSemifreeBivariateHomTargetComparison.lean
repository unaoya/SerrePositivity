module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGNerveTensorFixedFirst
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGSemifreeBivariateHomInfinity
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGSemifreeHomTensorComparison
/-!
概要：同じ二変数 D(R) 値 Hom の固定始域制限を、既存の共変 Hom と全関手同型で比較する。
方針：定値入力の非空切断を消し、同じ単位辺と空切断の実 cochain を使う。
規約：全単体・全面・退化を保持する。使われ方：二変数 Hom と既存 Hom の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped BigOperators _root_.Simplicial
variable (R : Type u) [CommRing R]
open CartesianMonoidalCategory
variable (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
/-- 元の固定入力における全単体作用の照合。 -/
def dgSemifreeDerivedHomProductDGop_targetIso (P : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (lift (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (Opposite.op P)))
        (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D)) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomProductDGopInfinity R D)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomTargetInfinity R D P) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomProductDGopInfinity
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorProductMap_second]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomTensor_targetIso R D P
/-- 元の固定入力における全単体作用の照合。 -/
def dgSemifreeDerivedHomBivariate_targetIso (P : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (lift (SSet.const (SSet.opObjEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex P : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D) _⦋0⦌)))
        (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D)) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomBivariateInfinity R D)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomTargetInfinity R D P) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomBivariateInfinity
  rw [← Category.assoc, lift_map, Category.id_comp,
    SSet.const_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveOppositeIso_hom_vertex]
  exact dgSemifreeDerivedHomProductDGop_targetIso R D P

end SerrePositivity.InfinityCategories.Project.DerivedCategories
