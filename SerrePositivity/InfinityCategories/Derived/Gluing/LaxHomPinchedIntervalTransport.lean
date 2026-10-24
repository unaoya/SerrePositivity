module
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomPullbackComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.PinchedIntervalPullbackTransport
/-!
概要：正本 lax Hom 標的を同じ入力の全区間 Hom 引き戻しへ同値に移す。
方針：F2 の矢印両端評価の持ち上げ性へ pinched・区間模型の厳密比較を適用する。
規約：元の二端点と第二射影を保持し、主経路へモデル圏の追加仮定を入れない。
使われ方：入力付き四座標比較の実逆射を正本比較へ輸送する第一段階。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory MonoidalClosed DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingLaxHomArrowVertex (X : DGGluingObject R C D M) :=
  (F2.laxPullbackArrow (dgGluingUniverseDerivedYoneda.{u, v, w} R C) (dgGluingUniverseDerivedCoefficient R C D M)).app (Opposite.op ⦋0⦌)
    (((dgGluingUniverseDerivedNerveLaxComparison R C D M)).app (Opposite.op ⦋0⦌) (ULift.up (Simplex.vertex X)))

def dgGluingLaxHomPinchedInputBase (X Y : DGGluingObject R C D M) :=
  pinchedHomPullbackBaseMap (F2.arrowEndpointPair ((SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj (dgModuleDerivedInfinityCategory R C))) ((dgGluingUniverseDerivedYoneda.{u, v, w} R C) ⊗ₘ (dgGluingUniverseDerivedCoefficient R C D M))
    (((dgGluingUniverseDerivedNerveLaxComparison R C D M)).app (Opposite.op ⦋0⦌) (ULift.up (Simplex.vertex X)))
    (((dgGluingUniverseDerivedNerveLaxComparison R C D M)).app (Opposite.op ⦋0⦌) (ULift.up (Simplex.vertex Y)))

def dgGluingLaxHomIntervalEndpointMap (X Y : DGGluingObject R C D M) :=
  intervalMappingPostOfEq (F2.arrowEndpointPair
    ((SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
      (dgModuleDerivedInfinityCategory R C)))
    (dgGluingLaxHomArrowVertex R C D M X) (dgGluingLaxHomArrowVertex R C D M Y) rfl rfl

def dgGluingLaxHomIntervalInputBase (X Y : DGGluingObject R C D M) :=
  dgGluingLaxHomPinchedInputBase R C D M X Y ≫ pinchedHomToIntervalMappingSpace _ _

def dgGluingLaxHomIntervalPullback (X Y : DGGluingObject R C D M) :=
  pullback (dgGluingLaxHomIntervalEndpointMap R C D M X Y)
    (dgGluingLaxHomIntervalInputBase R C D M X Y)

def dgGluingLaxHomPinchedIntervalTransport (X Y : DGGluingObject R C D M) :
    dgGluingLaxHomPullback R C D M X Y ⟶ dgGluingLaxHomIntervalPullback R C D M X Y :=
  dgGluingPinchedIntervalPullbackTransport (F2.arrowEndpointPair ((SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj (dgModuleDerivedInfinityCategory R C)))
    (dgGluingLaxHomArrowVertex R C D M X) (dgGluingLaxHomArrowVertex R C D M Y)
    (dgGluingLaxHomPinchedInputBase R C D M X Y)

lemma dgGluingLaxHomPinchedIntervalTransport_equivalence (X Y : DGGluingObject R C D M) :
    IsSimplicialHomotopyEquivalence (dgGluingLaxHomPinchedIntervalTransport R C D M X Y) := by
  letI : Quasicategory ((SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj (dgModuleDerivedInfinityCategory R C)) := inferInstance
  letI := F2.quasicategory_tensor
    ((SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj (dgModuleDerivedInfinityCategory R C))
    ((SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj (dgModuleDerivedInfinityCategory R C))
  letI := F2.quasicategory_tensor
    ((SSet.uliftFunctor.{max (u + 1) v w, max u v}).obj (dgNerve R C))
    ((SSet.uliftFunctor.{max (u + 1) v w, max u w}).obj (dgNerve R D))
  exact dgGluingPinchedIntervalPullbackTransport_equivalence (F2.arrowEndpointPair ((SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj (dgModuleDerivedInfinityCategory R C)))
    (dgGluingLaxHomArrowVertex R C D M X) (dgGluingLaxHomArrowVertex R C D M Y)
    (dgGluingLaxHomPinchedInputBase R C D M X Y)
    (F2.arrowEndpointPair_kanEquivalenceLifting ((SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj (dgModuleDerivedInfinityCategory R C)))

lemma dgGluingLaxHomPinchedIntervalTransport_arrow (X Y : DGGluingObject R C D M) :
    dgGluingLaxHomPinchedIntervalTransport R C D M X Y ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pinchedHomToIntervalMappingSpace _ _ :=
  pullback.lift_fst _ _ _

lemma dgGluingLaxHomPinchedIntervalTransport_inputs (X Y : DGGluingObject R C D M) :
    dgGluingLaxHomPinchedIntervalTransport R C D M X Y ≫ pullback.snd _ _ =
      pullback.snd _ _ := by
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)
end SerrePositivity.InfinityCategories
