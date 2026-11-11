module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.LaxPullbackFunctorCore
/-!
概要：同値持ち上げ性を持つ任意の一脚に沿う引き戻しを、全試験関手 core で表示する。
方針：内部 Hom の引き戻し保存と core の引き戻し同型を合成する。
規約：元の全二射影を保持する。使われ方：cospan の成分ごとの同値輸送。

対応節は Kerodon 5.5（Tag 01YV）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial

def functorCorePost (K : SSet.{u}) : SSet.{u} ⥤ SSet.{u} :=
  (ihom K) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor

variable {L M R : SSet.{u}} [Quasicategory L] [Quasicategory M] [Quasicategory R]
  (K : SSet.{u}) (f : L ⟶ M) (g : R ⟶ M) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting f)

def pullbackFunctorCoreIso :
    (functorCorePost K).obj (pullback f g) ≅
      pullback ((functorCorePost K).map f) ((functorCorePost K).map g) := by
  letI := hf.innerFibration
  letI : InnerFibration ((ihom K).map f) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting.innerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting.internalHom hf K)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.mapIso (PreservesPullback.iso (ihom K) f g) ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.corePullbackIso _ _

lemma pullbackFunctorCoreIso_fst :
    (pullbackFunctorCoreIso K f g hf).hom ≫ pullback.fst _ _ =
      (functorCorePost K).map (pullback.fst f g) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.map (PreservesPullback.iso (ihom K) f g).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.corePullbackMap _ _ ≫ pullback.fst _ _ = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.corePullbackMap_fst]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.map (PreservesPullback.iso (ihom K) f g).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.map (pullback.fst _ _) = _
  rw [← Functor.map_comp, PreservesPullback.iso_hom_fst]
  rfl

lemma pullbackFunctorCoreIso_snd :
    (pullbackFunctorCoreIso K f g hf).hom ≫ pullback.snd _ _ =
      (functorCorePost K).map (pullback.snd f g) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.map (PreservesPullback.iso (ihom K) f g).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.corePullbackMap _ _ ≫ pullback.snd _ _ = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.corePullbackMap_snd]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.map (PreservesPullback.iso (ihom K) f g).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.map (pullback.snd _ _) = _
  rw [← Functor.map_comp, PreservesPullback.iso_hom_snd]
  rfl

include hf in
lemma pullbackFunctorCore_first_fibration :
    HomotopicalAlgebra.Fibration ((functorCorePost K).map f) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.coreMap_fibration_of_kanEquivalenceLifting _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting.internalHom hf K)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
