module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.QuotientParameter
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.ContractionComparison

/-!
概要：固定した実懸垂商の二つの ε の交換欠損に、同じ商内の原始元を供給する。
方針：正本 strict data の contracted functor の微分等式を一般の二次補正へ渡す。
規約：欠損を境界として制御する。厳密な ε 整合や全入力作用の完成は主張しない。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction
open CategoryTheory DifferentialGraded KST.NonConnective HomologicalComplex
variable (R : Type u) [CommRing R] (C D : Type v)
  [DGCategory R C] [Small.{u} C] [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R C κ) (J : DGKappaConeInput R D κ)
  (F G : DGKappaSuspensionMapData R C D I J)
local notation "SC" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (DGKappaCone R C I)
  (dgKappaConePerfectObjects R C I)
local notation "CF" => _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionMapContractedFunctor R C D I J F
local notation "CG" => _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionMapContractedFunctor R C D I J G
/-- 正本 data の選択 ε に対する、同じ実商内の二次補正。 -/
def dgSuspensionContractionCorrection (b : SC)
    (t : zeroCycles (homObject R (DGKappaSuspension R D J)
      ((CF).toDGFunctor.obj b.val) ((CG).toDGFunctor.obj b.val))) :
    GradedHom R ((CF).toDGFunctor.obj b.val) ((CG).toDGFunctor.obj b.val) (-2) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgContractionCommutatorPrimitive R ((CF).homotopy b) ((CG).homotopy b) t

/-- 交換の欠損は、選択 ε を変えずに同じ商内で明示的な境界となる。 -/
lemma dgSuspensionContractionCorrection_d (b : SC)
    (t : zeroCycles (homObject R (DGKappaSuspension R D J)
      ((CF).toDGFunctor.obj b.val) ((CG).toDGFunctor.obj b.val))) :
    (homObject R (DGKappaSuspension R D J)
      ((CF).toDGFunctor.obj b.val) ((CG).toDGFunctor.obj b.val)).d (-2) (-1)
        (dgSuspensionContractionCorrection R C D I J F G b t) =
    forward R (p := -1) (q := 0) (n := -1) ((CF).homotopy b) t.val (by omega) -
      forward R (p := 0) (q := -1) (n := -1) t.val ((CG).homotopy b) (by omega) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgContractionCommutatorPrimitive_d R ((CF).homotopy b) ((CG).homotopy b) t
    ((CF).d_homotopy b) ((CG).d_homotopy b)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction
