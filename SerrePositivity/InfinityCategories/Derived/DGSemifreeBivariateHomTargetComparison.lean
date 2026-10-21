module
public import SerrePositivity.InfinityCategories.Derived.DGNerveTensorFixedFirst
public import SerrePositivity.InfinityCategories.Derived.DGSemifreeBivariateHomInfinity
public import SerrePositivity.InfinityCategories.Derived.DGSemifreeHomTensorComparison
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped BigOperators Simplicial
variable (R : Type u) [CommRing R]
open CartesianMonoidalCategory
variable (D : Type v) [DGCategory R D] [Small.{u} D]
/-- 元の固定入力における全単体作用の照合。 -/
def dgSemifreeDerivedHomProductDGop_targetIso (P : SemifreeDGModules R D) :
    FunctorIso
      (lift (SSet.const (Simplex.vertex (Opposite.op P)))
        (𝟙 (dgModuleDerivedInfinityCategory R D)) ≫ dgSemifreeDerivedHomProductDGopInfinity R D)
      (dgSemifreeDerivedHomTargetInfinity R D P) := by
  unfold dgSemifreeDerivedHomProductDGopInfinity
  rw [← Category.assoc, dgNerveTensorProductMap_second]
  exact dgSemifreeDerivedHomTensor_targetIso R D P
/-- 元の固定入力における全単体作用の照合。 -/
def dgSemifreeDerivedHomBivariate_targetIso (P : SemifreeDGModules R D) :
    FunctorIso
      (lift (SSet.const (SSet.opObjEquiv.symm
        (Simplex.vertex P : (dgModuleDerivedInfinityCategory R D) _⦋0⦌)))
        (𝟙 (dgModuleDerivedInfinityCategory R D)) ≫ dgSemifreeDerivedHomBivariateInfinity R D)
      (dgSemifreeDerivedHomTargetInfinity R D P) := by
  unfold dgSemifreeDerivedHomBivariateInfinity
  rw [← Category.assoc, lift_map, Category.id_comp,
    SSet.const_comp, dgNerveOppositeIso_hom_vertex]
  exact dgSemifreeDerivedHomProductDGop_targetIso R D P

end SerrePositivity.InfinityCategories
