module
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackFunctorCore
/-!
概要：同値持ち上げ性を持つ任意の一脚に沿う引き戻しを、全試験関手 core で表示する。
方針：内部 Hom の引き戻し保存と core の引き戻し同型を合成する。
規約：元の全二射影を保持する。使われ方：cospan の成分ごとの同値輸送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.F2
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open SSet.modelCategoryQuillen
open scoped Simplicial

def functorCorePost (K : SSet.{u}) : SSet.{u} ⥤ SSet.{u} :=
  (ihom K) ⋙ quasicategoryCoreFunctor

variable {L M R : SSet.{u}} [Quasicategory L] [Quasicategory M] [Quasicategory R]
  (K : SSet.{u}) (f : L ⟶ M) (g : R ⟶ M) (hf : F1B.EquivalenceLifting f)

def pullbackFunctorCoreIso :
    (functorCorePost K).obj (pullback f g) ≅
      pullback ((functorCorePost K).map f) ((functorCorePost K).map g) := by
  letI := hf.innerFibration
  letI : InnerFibration ((ihom K).map f) :=
    F1B.EquivalenceLifting.innerFibration (F1B.EquivalenceLifting.internalHom hf K)
  exact quasicategoryCoreFunctor.mapIso (PreservesPullback.iso (ihom K) f g) ≪≫
    corePullbackIso _ _

lemma pullbackFunctorCoreIso_fst :
    (pullbackFunctorCoreIso K f g hf).hom ≫ pullback.fst _ _ =
      (functorCorePost K).map (pullback.fst f g) := by
  change quasicategoryCoreFunctor.map (PreservesPullback.iso (ihom K) f g).hom ≫
    corePullbackMap _ _ ≫ pullback.fst _ _ = _
  rw [corePullbackMap_fst]
  change quasicategoryCoreFunctor.map (PreservesPullback.iso (ihom K) f g).hom ≫
    quasicategoryCoreFunctor.map (pullback.fst _ _) = _
  rw [← Functor.map_comp, PreservesPullback.iso_hom_fst]
  rfl

lemma pullbackFunctorCoreIso_snd :
    (pullbackFunctorCoreIso K f g hf).hom ≫ pullback.snd _ _ =
      (functorCorePost K).map (pullback.snd f g) := by
  change quasicategoryCoreFunctor.map (PreservesPullback.iso (ihom K) f g).hom ≫
    corePullbackMap _ _ ≫ pullback.snd _ _ = _
  rw [corePullbackMap_snd]
  change quasicategoryCoreFunctor.map (PreservesPullback.iso (ihom K) f g).hom ≫
    quasicategoryCoreFunctor.map (pullback.snd _ _) = _
  rw [← Functor.map_comp, PreservesPullback.iso_hom_snd]
  rfl

include hf in
lemma pullbackFunctorCore_first_fibration :
    HomotopicalAlgebra.Fibration ((functorCorePost K).map f) :=
  coreMap_fibration_of_kanEquivalenceLifting _ (F1B.EquivalenceLifting.internalHom hf K)

end SerrePositivity.InfinityCategories.F2
