module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackLimit
public import SerrePositivity.InfinityCategories.F1.CatInfinity.CorePullbackIso
public import SerrePositivity.InfinityCategories.F1B.CatInfinity.CoreIsofibration
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
概要：lax pullback への全試験関手 core の引き戻し表示。
方針：内部 Hom の引き戻し保存と core の交換同型を使う。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

variable {A B C : SSet.{u}}
/-- 概要：全試験関手 core の比較は矢印の族と二対象の入力を保持する。
方針：内部 Hom の引き戻し保存と core の交換同型の射影を計算する。
規約：K に quasicategory 性を仮定しない。
使われ方：lax pullback の写像空間による普遍性。 -/
def laxPullbackFunctorIso (K : SSet.{u}) (p : A ⟶ C) (q : B ⟶ C) :
    (ihom K).obj (laxPullback p q) ≅
      pullback ((ihom K).map (arrowEndpointPair C)) ((ihom K).map (p ⊗ₘ q)) :=
  PreservesPullback.iso (ihom K) _ _
variable [Quasicategory A] [Quasicategory B] [Quasicategory C]
attribute [local instance] quasicategory_tensor
/-- 概要：全試験関手 core の比較は矢印の族と二対象の入力を保持する。
方針：内部 Hom の引き戻し保存と core の交換同型の射影を計算する。
規約：K に quasicategory 性を仮定しない。
使われ方：lax pullback の写像空間による普遍性。 -/
def laxPullbackFunctorCoreIso (K : SSet.{u}) (p : A ⟶ C) (q : B ⟶ C) :
    (quasicategoryCore ((ihom K).obj (laxPullback p q)) : SSet.{u}) ≅
      pullback (quasicategoryCoreMap ((ihom K).map (arrowEndpointPair C)))
        (quasicategoryCoreMap ((ihom K).map (p ⊗ₘ q))) :=
  quasicategoryCoreFunctor.mapIso (laxPullbackFunctorIso K p q) ≪≫
    corePullbackIso _ _
/-- 概要：全試験関手 core の比較は矢印の族と二対象の入力を保持する。
方針：内部 Hom の引き戻し保存と core の交換同型の射影を計算する。
規約：K に quasicategory 性を仮定しない。
使われ方：lax pullback の写像空間による普遍性。 -/
lemma laxPullbackFunctorCoreIso_arrow (K : SSet.{u}) (p : A ⟶ C) (q : B ⟶ C) :
    (laxPullbackFunctorCoreIso K p q).hom ≫
      pullback.fst (quasicategoryCoreMap ((ihom K).map (arrowEndpointPair C)))
        (quasicategoryCoreMap ((ihom K).map (p ⊗ₘ q))) =
      quasicategoryCoreMap ((ihom K).map (laxPullbackArrow p q)) := by
  change quasicategoryCoreFunctor.map (PreservesPullback.iso (ihom K) _ _).hom ≫
    corePullbackMap _ _ ≫ pullback.fst _ _ = _
  rw [corePullbackMap_fst]
  change quasicategoryCoreFunctor.map (PreservesPullback.iso (ihom K) _ _).hom ≫
    quasicategoryCoreFunctor.map (pullback.fst _ _) = _
  rw [← CategoryTheory.Functor.map_comp, PreservesPullback.iso_hom_fst]
  rfl
/-- 概要：全試験関手 core の比較は矢印の族と二対象の入力を保持する。
方針：内部 Hom の引き戻し保存と core の交換同型の射影を計算する。
規約：K に quasicategory 性を仮定しない。
使われ方：lax pullback の写像空間による普遍性。 -/
lemma laxPullbackFunctorCoreIso_inputs (K : SSet.{u}) (p : A ⟶ C) (q : B ⟶ C) :
    (laxPullbackFunctorCoreIso K p q).hom ≫
      pullback.snd (quasicategoryCoreMap ((ihom K).map (arrowEndpointPair C)))
        (quasicategoryCoreMap ((ihom K).map (p ⊗ₘ q))) =
      quasicategoryCoreMap ((ihom K).map (pullback.snd (arrowEndpointPair C) (p ⊗ₘ q))) := by
  change quasicategoryCoreFunctor.map (PreservesPullback.iso (ihom K) _ _).hom ≫
    corePullbackMap _ _ ≫ pullback.snd _ _ = _
  rw [corePullbackMap_snd]
  change quasicategoryCoreFunctor.map (PreservesPullback.iso (ihom K) _ _).hom ≫
    quasicategoryCoreFunctor.map (pullback.snd _ _) = _
  rw [← CategoryTheory.Functor.map_comp, PreservesPullback.iso_hom_snd]
  rfl
/-- 概要：全試験関手 core の比較は矢印の族と二対象の入力を保持する。
方針：内部 Hom の引き戻し保存と core の交換同型の射影を計算する。
規約：K に quasicategory 性を仮定しない。
使われ方：lax pullback の写像空間による普遍性。 -/
lemma arrowEndpointPair_internalHom_core_fibration (K : SSet.{u}) :
    HomotopicalAlgebra.Fibration (quasicategoryCoreMap ((ihom K).map (arrowEndpointPair C))) :=
  coreMap_fibration_of_kanEquivalenceLifting _
    (SerrePositivity.InfinityCategories.F1B.EquivalenceLifting.internalHom (arrowEndpointPair_kanEquivalenceLifting C) K)

end SerrePositivity.InfinityCategories.F2
