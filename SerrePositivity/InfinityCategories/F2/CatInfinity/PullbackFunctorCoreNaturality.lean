module
public import SerrePositivity.InfinityCategories.F2.CatInfinity.PullbackFunctorCoreIso
/-!
概要：厳密可換な cospan 比較の元 pullback.map を全試験関手 core の同じ三成分へ移す。
方針：二つの射影と関手則で自然性を厳密に証明する。
規約：比較の元の射を変更しない。使われ方：成分ごとの同値から実引き戻し比較へ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.F2
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
variable {L M R L' M' R' : SSet.{u}}
  [Quasicategory L] [Quasicategory M] [Quasicategory R]
  [Quasicategory L'] [Quasicategory M'] [Quasicategory R']
  (K : SSet.{u}) (f : L ⟶ M) (g : R ⟶ M) (f' : L' ⟶ M') (g' : R' ⟶ M')
  (s : L ⟶ L') (t : R ⟶ R') (v : M ⟶ M')
  (hs : f ≫ v = s ≫ f') (ht : g ≫ v = t ≫ g')

def pullbackFunctorCoreMap :
    pullback ((functorCorePost K).map f) ((functorCorePost K).map g) ⟶
      pullback ((functorCorePost K).map f') ((functorCorePost K).map g') :=
  pullback.map _ _ _ _ ((functorCorePost K).map s) ((functorCorePost K).map t)
    ((functorCorePost K).map v)
    (by simpa only [Functor.map_comp] using congrArg (functorCorePost K).map hs)
    (by simpa only [Functor.map_comp] using congrArg (functorCorePost K).map ht)

lemma pullbackFunctorCoreIso_naturality (hf : F1B.EquivalenceLifting f)
    (hf' : F1B.EquivalenceLifting f') :
    (functorCorePost K).map (pullback.map f g f' g' s t v hs ht) ≫
      (pullbackFunctorCoreIso K f' g' hf').hom =
    (pullbackFunctorCoreIso K f g hf).hom ≫ pullbackFunctorCoreMap K f g f' g' s t v hs ht := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackFunctorCoreIso_fst, ← Functor.map_comp,
      pullback.map, pullback.lift_fst, Functor.map_comp]
    rw [Category.assoc, pullbackFunctorCoreMap, pullback.lift_fst,
      ← Category.assoc, pullbackFunctorCoreIso_fst]
  · rw [Category.assoc, pullbackFunctorCoreIso_snd, ← Functor.map_comp,
      pullback.map, pullback.lift_snd, Functor.map_comp]
    rw [Category.assoc, pullbackFunctorCoreMap, pullback.lift_snd,
      ← Category.assoc, pullbackFunctorCoreIso_snd]

end SerrePositivity.InfinityCategories.F2
