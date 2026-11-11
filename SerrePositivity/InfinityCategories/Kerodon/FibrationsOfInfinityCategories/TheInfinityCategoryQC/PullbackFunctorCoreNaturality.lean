module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PullbackFunctorCoreIso
/-!
概要：厳密可換な cospan 比較の元 pullback.map を全試験関手 core の同じ三成分へ移す。
方針：二つの射影と関手則で自然性を厳密に証明する。
規約：比較の元の射を変更しない。使われ方：成分ごとの同値から実引き戻し比較へ。

対応節は Kerodon 5.5（Tag 01YV）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
variable {L M R L' M' R' : SSet.{u}}
  [Quasicategory L] [Quasicategory M] [Quasicategory R]
  [Quasicategory L'] [Quasicategory M'] [Quasicategory R']
  (K : SSet.{u}) (f : L ⟶ M) (g : R ⟶ M) (f' : L' ⟶ M') (g' : R' ⟶ M')
  (s : L ⟶ L') (t : R ⟶ R') (v : M ⟶ M')
  (hs : f ≫ v = s ≫ f') (ht : g ≫ v = t ≫ g')

def pullbackFunctorCoreMap :
    pullback ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorCorePost K).map f) ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorCorePost K).map g) ⟶
      pullback ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorCorePost K).map f') ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorCorePost K).map g') :=
  pullback.map _ _ _ _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorCorePost K).map s) ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorCorePost K).map t)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorCorePost K).map v)
    (by simpa only [Functor.map_comp] using congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorCorePost K).map hs)
    (by simpa only [Functor.map_comp] using congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorCorePost K).map ht)

lemma pullbackFunctorCoreIso_naturality (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting f)
    (hf' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting f') :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorCorePost K).map (pullback.map f g f' g' s t v hs ht) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pullbackFunctorCoreIso K f' g' hf').hom =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pullbackFunctorCoreIso K f g hf).hom ≫ pullbackFunctorCoreMap K f g f' g' s t v hs ht := by
  apply pullback.hom_ext
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pullbackFunctorCoreIso_fst, ← Functor.map_comp,
      pullback.map, pullback.lift_fst, Functor.map_comp]
    rw [Category.assoc, pullbackFunctorCoreMap, pullback.lift_fst,
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pullbackFunctorCoreIso_fst]
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pullbackFunctorCoreIso_snd, ← Functor.map_comp,
      pullback.map, pullback.lift_snd, Functor.map_comp]
    rw [Category.assoc, pullbackFunctorCoreMap, pullback.lift_snd,
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pullbackFunctorCoreIso_snd]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
