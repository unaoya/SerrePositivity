module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransportAlgebra

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedRightFamilyActionNaturality
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorIsoPairTensor
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoChainTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorIsoTransportAlgebra

/-!
概要：全右 Hom 比較の輸送作用を、元の始点同型と元の普遍輸送の終点の作用へ同定する。
方針：同じ全直積の作用を直積射と同じ終点射に分解し、指定同型の直積自然性を使う。
規約：元の輸送証人と指定値を保持。使われ方：値比較の元の始点単位因子との照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2
variable {K L : KanObject.{u}} {P : SSet.{u + 1}}
local notation "A" => CategoryTheory.Functor.obj SSet.uliftFunctor (KanObject.obj K)
local notation "H" => CategoryTheory.Functor.obj SSet.uliftFunctor (SimplicialCategory.sHom K L)
local notation "N" => diagonalFiberTransport pointedSpaceProjection
  (fst A H ≫ pointedRightFiberComparison K) (snd A H ≫ coherentKanRightHomInterval K L)
local notation "d" => pointedRightFiberComparison K ⊗ₘ coherentKanRightHomInterval K L
local notation "E" => FiberTransportFamily.endpoint (parametrizedFiberTransportFamily
  pointedSpaceProjection (spaceInfinityVertex K) (spaceInfinityVertex L))

/-- 元の全直積上の輸送作用は、同じ二作用の直積と元の普遍輸送終点の合成。 -/
lemma pointedRightFamilyUniversal_transport_map : N = d ≫ E := by
  change lift (fst A H ≫ pointedRightFiberComparison K)
    (snd A H ≫ coherentKanRightHomInterval K L) ≫ E = d ≫ E
  rw [lift_fst_comp_snd_comp]

variable {x x' : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj K.obj} (a : FunctorIso x x')
  (y : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L))

/-- 指定輸送作用は、元の始点同型と区間の組に元の普遍終点を作用させた指定値。 -/
lemma pointedRightFamilyTransportActionIso_heq_source :
    HEq (pointedRightFamilyTransportActionIso a y)
      ((functorIsoLiftRight (a.postcomp (pointedRightFiberComparison K))
        (y ≫ coherentKanRightHomInterval K L)).postcomp E) := by
  have hp := functorIsoOfEq_heq ((functorIsoLiftRight a y).postcomp N)
    (pointedRightFamilyUniversal_target x y) (pointedRightFamilyUniversal_target x' y)
  have hm := functorIso_postcomp_heq_of_map_eq (functorIsoLiftRight a y)
    (pointedRightFamilyUniversal_transport_map (K := K) (L := L))
  have ht := functorIsoLiftRight_tensor_heq a y (pointedRightFiberComparison K)
    (coherentKanRightHomInterval K L)
  have hE := functorIso_postcomp_heq_of_heq ((functorIsoLiftRight a y).postcomp d)
    (functorIsoLiftRight (a.postcomp (pointedRightFiberComparison K))
      (y ≫ coherentKanRightHomInterval K L))
    (lift_map x y (pointedRightFiberComparison K) (coherentKanRightHomInterval K L))
    (lift_map x' y (pointedRightFiberComparison K) (coherentKanRightHomInterval K L)) ht.symm E
  exact hp.trans (hm.symm.trans
    ((heq_of_eq (functorIso_postcomp_postcomp (functorIsoLiftRight a y) d E)).symm.trans hE.symm))

end SerrePositivity.InfinityCategories.F2
