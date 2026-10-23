module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.CorePullbackIso

/-!
概要：引き戻し候補への全試験関手 core の厳密な引き戻し表示。
方針：関手単体集合との交換同型に core を適用し、inner fibration の core 比較と合成する。
規約：右辺の第一関手は可逆 path 置換後の core であり、元の第一関手の core と区別する。
使われ方：Cat_∞ の引き戻しの写像空間の普遍性に向けた全次数の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2

variable {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]

/-- 概要：候補への任意の試験 K からの関手 core は置換した core の引き戻しと同型。
方針：関手空間との交換と core の引き戻し比較を合成する。
規約：K の quasicategory 性は不要で、全ての単体の族を比較する。
使われ方：全試験 ∞ 圏に対する写像空間の引き戻し表示の入力。 -/
def catPullbackFunctorCoreIso (K : SSet.{u}) (p : A ⟶ C) (q : B ⟶ C) :
    (quasicategoryCore ((ihom K).obj (catPullback p q)) : SSet.{u}) ≅
      pullback (quasicategoryCoreMap (equivalencePathReplacementMap ((ihom K).map p)))
        (quasicategoryCoreMap ((ihom K).map q)) :=
  quasicategoryCoreFunctor.mapIso (catPullbackFunctorIso K p q) ≪≫
    corePullbackIso (equivalencePathReplacementMap ((ihom K).map p)) ((ihom K).map q)

/-- 概要：全試験関手 core の同型は第二射影の後合成と可換。
方針：core 比較の第二射影と関手空間比較の第二射影を合成する。
規約：元の q の始域への射影を厳密に保つ。
使われ方：写像空間の普遍性と元の錐の第二の脚の照合。 -/
lemma catPullbackFunctorCoreIso_snd (K : SSet.{u}) (p : A ⟶ C) (q : B ⟶ C) :
    (catPullbackFunctorCoreIso K p q).hom ≫
      pullback.snd (quasicategoryCoreMap (equivalencePathReplacementMap ((ihom K).map p)))
        (quasicategoryCoreMap ((ihom K).map q)) =
      quasicategoryCoreMap ((ihom K).map (catPullbackSnd p q)) := by
  change quasicategoryCoreFunctor.map (catPullbackFunctorMap K p q) ≫
    corePullbackMap _ _ ≫ pullback.snd _ _ = _
  rw [corePullbackMap_snd]
  change quasicategoryCoreFunctor.map (catPullbackFunctorMap K p q) ≫
    quasicategoryCoreFunctor.map (catPullbackSnd ((ihom K).map p) ((ihom K).map q)) = _
  rw [← Functor.map_comp]
  exact congrArg quasicategoryCoreFunctor.map (catPullbackFunctorMap_snd K p q)

/-- 概要：全試験関手 core の同型は置換の射影を通して元の第一射影を保つ。
方針：core 比較の第一射影と置換の射影を関手空間の第一射影へまとめる。
規約：第一の core は置換後の対象なので、元の A への射影を明示する。
使われ方：写像空間の普遍性と元の錐の第一の脚の照合。 -/
lemma catPullbackFunctorCoreIso_fst (K : SSet.{u}) (p : A ⟶ C) (q : B ⟶ C) :
    (catPullbackFunctorCoreIso K p q).hom ≫
      pullback.fst (quasicategoryCoreMap (equivalencePathReplacementMap ((ihom K).map p)))
        (quasicategoryCoreMap ((ihom K).map q)) ≫
          quasicategoryCoreMap (equivalencePathReplacementProjection ((ihom K).map p)) =
      quasicategoryCoreMap ((ihom K).map (catPullbackFst p q)) := by
  change quasicategoryCoreFunctor.map (catPullbackFunctorMap K p q) ≫
    corePullbackMap _ _ ≫ pullback.fst _ _ ≫
      quasicategoryCoreFunctor.map (equivalencePathReplacementProjection ((ihom K).map p)) = _
  rw [corePullbackMap_fst_assoc]
  change quasicategoryCoreFunctor.map (catPullbackFunctorMap K p q) ≫
    quasicategoryCoreFunctor.map (pullback.fst (equivalencePathReplacementMap ((ihom K).map p))
      ((ihom K).map q)) ≫
        quasicategoryCoreFunctor.map (equivalencePathReplacementProjection ((ihom K).map p)) = _
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg quasicategoryCoreFunctor.map (catPullbackFunctorMap_fst K p q)

end SerrePositivity.InfinityCategories.F2
