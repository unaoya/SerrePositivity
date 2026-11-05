module
public import SerrePositivity.InfinityCategories.HomotopyLimits.KanLimits
public import SerrePositivity.InfinityCategories.F2.CatInfinity.PullbackFunctorCoreNaturality
public import SerrePositivity.InfinityCategories.F2.CatInfinity.PostcompositionCoreDetection
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.StrictKanPullbackMapEquivalence
public import SerrePositivity.InfinityCategories.F1.Categories.CoreEquivalence
public import SerrePositivity.InfinityCategories.Core.FunctorComposition
/-!
概要：同値持ち上げ性を持つ二つの cospan の成分同値は、同じ pullback.map を圏同値にする。
方針：全試験関手 core で同じ三成分の Kan 引き戻し比較へ移し、元の射へ反映する。
規約：元の比較射・二射影・厳密な可換条件を保持する。
使われ方：元二脚と固定 ν 二脚の lax 模型を結ぶ一般輸送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.F2
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial
variable {L M R L' M' R' : SSet.{u}}
  [Quasicategory L] [Quasicategory M] [Quasicategory R]
  [Quasicategory L'] [Quasicategory M'] [Quasicategory R']
  (f : L ⟶ M) (g : R ⟶ M) (f' : L' ⟶ M') (g' : R' ⟶ M')
  (s : L ⟶ L') (t : R ⟶ R') (v : M ⟶ M')
  (hs : f ≫ v = s ≫ f') (ht : g ≫ v = t ≫ g')

variable [InnerFibration f] [InnerFibration f']

lemma pullbackMap_isQCatEquivalence_of_components
    (hf : F1B.EquivalenceLifting f) (hf' : F1B.EquivalenceLifting f')
    (es : IsQCatEquivalence s) (et : IsQCatEquivalence t) (ev : IsQCatEquivalence v) :
    IsQCatEquivalence (pullback.map f g f' g' s t v hs ht) := by
  letI := hf.innerFibration
  letI := hf'.innerFibration
  apply isQCatEquivalence_of_postcomposition_core
  intro K
  letI : KanComplex ((functorCorePost K).obj L) := by
    change KanComplex (quasicategoryCore ((ihom K).obj L) : SSet.{u}); infer_instance
  letI : KanComplex ((functorCorePost K).obj M) := by
    change KanComplex (quasicategoryCore ((ihom K).obj M) : SSet.{u}); infer_instance
  letI : KanComplex ((functorCorePost K).obj R) := by
    change KanComplex (quasicategoryCore ((ihom K).obj R) : SSet.{u}); infer_instance
  letI : KanComplex ((functorCorePost K).obj L') := by
    change KanComplex (quasicategoryCore ((ihom K).obj L') : SSet.{u}); infer_instance
  letI : KanComplex ((functorCorePost K).obj M') := by
    change KanComplex (quasicategoryCore ((ihom K).obj M') : SSet.{u}); infer_instance
  letI : KanComplex ((functorCorePost K).obj R') := by
    change KanComplex (quasicategoryCore ((ihom K).obj R') : SSet.{u}); infer_instance
  letI := pullbackFunctorCore_first_fibration K f hf
  letI := pullbackFunctorCore_first_fibration K f' hf'
  have hsK : (functorCorePost K).map f ≫ (functorCorePost K).map v =
      (functorCorePost K).map s ≫ (functorCorePost K).map f' := by
    simpa only [Functor.map_comp] using congrArg (functorCorePost K).map hs
  have htK : (functorCorePost K).map g ≫ (functorCorePost K).map v =
      (functorCorePost K).map t ≫ (functorCorePost K).map g' := by
    simpa only [Functor.map_comp] using congrArg (functorCorePost K).map ht
  have he : IsSimplicialHomotopyEquivalence
      (pullbackFunctorCoreMap K f g f' g' s t v hs ht) :=
    strictKanPullbackMap_homotopyEquivalence _ _ _ _ _ _ _ hsK htK
      ((es.postcompose K).core.isSimplicialHomotopyEquivalence)
      ((et.postcompose K).core.isSimplicialHomotopyEquivalence)
      ((ev.postcompose K).core.isSimplicialHomotopyEquivalence)
  letI : KanComplex ((functorCorePost K).obj (pullback f g)) := by
    change KanComplex (quasicategoryCore ((ihom K).obj (pullback f g)) : SSet.{u}); infer_instance
  letI : KanComplex ((functorCorePost K).obj (pullback f' g')) := by
    change KanComplex (quasicategoryCore ((ihom K).obj (pullback f' g')) : SSet.{u}); infer_instance
  letI : KanComplex (pullback ((functorCorePost K).map f) ((functorCorePost K).map g)) :=
    HomotopyLimits.pullback_kanComplex_of_fibration _ _
  letI : KanComplex (pullback ((functorCorePost K).map f') ((functorCorePost K).map g')) :=
    HomotopyLimits.pullback_kanComplex_of_fibration _ _
  have hcomp : IsQCatEquivalence
      ((functorCorePost K).map (pullback.map f g f' g' s t v hs ht) ≫
        (pullbackFunctorCoreIso K f' g' hf').hom) := by
    rw [pullbackFunctorCoreIso_naturality K f g f' g' s t v hs ht hf hf']
    exact (qCatEquivalenceOfIso (pullbackFunctorCoreIso K f g hf)).isQCatEquivalence.comp
      he.isQCatEquivalence
  exact (qCatEquivalenceOfIso (pullbackFunctorCoreIso K f' g' hf')).isQCatEquivalence.cancel_right
    hcomp

end SerrePositivity.InfinityCategories.F2
